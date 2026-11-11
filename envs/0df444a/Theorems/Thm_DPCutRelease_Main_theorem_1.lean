-- Prove2me | Theorems.Thm_DPCutRelease_Main_theorem_1
-- name    : DPCutRelease.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:12:39.052995+00:00
-- url     : https://prove2.me/theorems/26133e4d-4e1f-440c-904a-89d4ac41121e
-- title:
--   Theorem 1 — a polynomial-time (ε, δ)-edge-DP real-RAM program releasing every cut up to γ·w(S) + O((n/γε)·log⁷(n/δβγε))
-- statement:
--   Let $n\ge2$, $0<\gamma\le1/4$, $0<\varepsilon\le1$ and $0<\delta,\beta<1/10$. There is an $(\varepsilon,\delta)$ edge-DP algorithm that, on every nonnegative weighted $n$-vertex graph $G$ (weights $w\in\mathbb R_{\ge0}^{\binom n2}$), runs in time polynomial in $n,1/\gamma,1/\varepsilon,\log(1/\delta),\log(1/\beta)$ and outputs a nonnegative weighted graph $\tilde G$ satisfying, with probability at least $1-\beta$, simultaneously for every $S\subseteq V$,
--   $$\big|w_G(S,V\setminus S)-w_{\tilde G}(S,V\setminus S)\big|\le\gamma\,w_G(S,V\setminus S)+O\Big(\frac n{\gamma\varepsilon}\big(\log(n/(\delta\beta\gamma\varepsilon))\big)^7\Big).$$
--
--   Formally: there are one admissible program $P$ of the real RAM of §1.1.1, one universal constant $C>0$ and constants $C'>0$, $d\in\mathbb N$, all fixed before any input, such that for every $n\ge2$, $\gamma,\varepsilon,\delta,\beta$ in the ranges above and every $w\ge0$:
--   1. every run of $P$ on $(n,\gamma,\varepsilon,\delta,\beta,w)$ halts within $C'\,(n\gamma^{-1}\varepsilon^{-1}\log(1/\delta)\log(1/\beta))^d$ steps;
--   2. the output $\tilde w$ is a measurable function of the tape and is nonnegative on every run;
--   3. the set of tapes on which some $S\subseteq[n]$ has $|w(S,V\setminus S)-\tilde w(S,V\setminus S)|>\gamma\,w(S,V\setminus S)+C\frac n{\gamma\varepsilon}(\log\frac n{\delta\beta\gamma\varepsilon})^7$ has measure at most $\beta$;
--   4. for all adjacent $w,w'\ge0$ ($\|w-w'\|_1\le1$) and every measurable $A$, $\Pr[P(w)\in A]\le e^\varepsilon\Pr[P(w')\in A]+\delta$.
--
--   This is the paper's central result: the first polynomial-time edge-private release with relative error $\gamma$ and additive error $\tilde O(n)$ on all cuts. The proof composes Algorithm 4 (Lemma 12) with Algorithm 1 (Lemmas 18, 23) and implements the SDP by the ellipsoid method (pp. 33–34).
--
--   **Formalization Note.** The machine, `inputState`, `finalOutput`, `HaltsWithin` and `tape` are in `Def_DPCutRelease_Main_Machine`; cut values and `IsEdgeDPFun` in `Def_DPCutRelease_Main_EdgeDP`. No instruction solves an SDP, takes an eigenvalue, inverts a matrix or reads $w$ as a function.
--
--   Differences from the source:
--   - reading: "Let n ≥ 2, 0 < γ ≤ 1/4, … There is an (ε, δ) edge-DP algorithm … O(·)" → ∃ one program P, one C, one (C′, d) before n, γ, ε, δ, β, w; reason: "runs in time polynomial in n, 1/γ, 1/ε, log(1/δ), log(1/β)" only has content uniformly; p. 34 states the constant is uniform over the parameter range
--   - reading: "algorithm … runs in time polynomial" → an Admissible program of the real RAM of §1.1.1 (Machine module); time = executed instructions, worst case on every pair of streams; reason: §1.1.1 names the model; footnote 2 bounds "the running time on every execution"
--   - encoding: "time polynomial in n, 1/γ, 1/ε, log(1/δ), log(1/β)" → HaltsWithin P s₀ (C′·(n γ⁻¹ ε⁻¹ log(1/δ) log(1/β))^d); reason: every factor is ≥ 1 on the parameter range (log(1/δ), log(1/β) > log 10 > 1), so every polynomial is bounded by such a monomial
--   - encoding: the algorithm’s output law → conjunct Measurable (finalOutput …) and DP stated on tape preimages (IsEdgeDPFun tape …); reason: rules out a vacuous DP statement through Measure.map of a non-measurable run
--   - encoding: input graph G and output graph G̃ → inputState n γ ε δ β w (p[0] = n, cells 0–3 = γ, ε, δ, β, cell 4 + n·u + v = w_{uv}); output cell −1 − (n·u + v); reason: a fixed public layout; the parameters are public inputs (Algorithm 1’s input line)
--   - encoding: edge coordinates {u, v} ∈ ([n] choose 2), vertex set [n] → Pair n = {(u, v) : Fin n × Fin n // u < v}, 0-based; reason: one coordinate per unordered pair, same instances
--   - encoding: with probability at least 1 − p → the noise/tape measure of the failure set is at most p (outer measure if the set were not measurable); reason: same statement for measurable events; cannot be made vacuous by non-measurability
--   - encoding: Pr[M(w) ∈ A] ≤ e^ε Pr[M(w′) ∈ A] + δ for adjacent w, w′ and measurable A, and symmetrically → IsEdgeDP / IsEdgeDPFun: the inequality between real numbers (toReal) for every ordered adjacent pair; reason: adjacency is symmetric, so the swapped clause is the same condition; every law involved is a probability measure
-- source:
--   Eliáš et al., Polynomial-Time Differentially Private Synthetic Graph Release with Nearly-Linear Additive Error, arXiv:2611.06670v1, p. 2–3, Theorem 1 (proof pp. 33–34)

import Mathlib
import Definitions.Def_DPCutRelease_Main_EdgeDP
import Definitions.Def_DPCutRelease_Main_Machine

open MeasureTheory

namespace DPCutRelease.Main

/-- Theorem 1 (p. 2–3): one admissible program `P` of the real RAM of §1.1.1, one universal error
constant `C` and one polynomial `C'·(·)^d` such that for every `n ≥ 2`, `0 < γ ≤ 1/4`, `0 < ε ≤ 1`,
`0 < δ, β < 1/10` and every nonnegative `w`: every run halts within
`C'(n γ⁻¹ ε⁻¹ log(1/δ) log(1/β))^d` steps, the output is a measurable function of the tape and
nonnegative on every run, and the tapes on which some cut has
`|w(S) − w̃(S)| > γ w(S) + C (n/(γε)) (log(n/(δβγε)))⁷` have measure at most `β`; and the output is
`(ε, δ)` edge-DP. -/
theorem theorem_1 :
    ∃ P : Program, Admissible P ∧ ∃ C C' : ℝ, 0 < C ∧ 0 < C' ∧ ∃ d : ℕ,
      ∀ (n : ℕ) (γ ε δ β : ℝ), 2 ≤ n → 0 < γ → γ ≤ 1 / 4 → 0 < ε → ε ≤ 1 →
        0 < δ → δ < 1 / 10 → 0 < β → β < 1 / 10 →
        (∀ w : EdgeVec n, Nonneg w →
          HaltsWithin P (inputState n γ ε δ β w)
            (C' * ((n : ℝ) * γ⁻¹ * ε⁻¹ * Real.log (1 / δ) * Real.log (1 / β)) ^ d) ∧
          Measurable (finalOutput n P (inputState n γ ε δ β w)) ∧
          (∀ ω e, 0 ≤ finalOutput n P (inputState n γ ε δ β w) ω e) ∧
          tape {ω | ∃ S : Finset (Fin n),
              γ * cutValue w S + C * ((n : ℝ) / (γ * ε)) * Real.log (n / (δ * β * γ * ε)) ^ 7 <
                |cutValue w S - cutValue (finalOutput n P (inputState n γ ε δ β w) ω) S|}
            ≤ ENNReal.ofReal β) ∧
        IsEdgeDPFun tape (fun w ω => finalOutput n P (inputState n γ ε δ β w) ω) ε δ := by sorry

end DPCutRelease.Main
