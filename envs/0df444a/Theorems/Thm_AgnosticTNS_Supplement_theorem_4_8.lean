-- Prove2me | Theorems.Thm_AgnosticTNS_Supplement_theorem_4_8
-- name    : AgnosticTNS.Supplement.theorem_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T01:44:55.647301+00:00
-- url     : https://prove2.me/theorems/5ff2b7aa-3a9c-4af9-bfa3-b001861bda95
-- title:
--   Theorem 4.8 — tomography using a learning sequence
-- statement:
--   Let $G=([n],E)$ be a graph, $\chi\ge1$, $d\ge2$, and $\mathcal L=(S_i,I_i,F_i)_{i=1}^L$ a learning sequence for $G$; put $r_i=\chi^{|\mathrm{cut}_G(S_i)|}$ (4.41), $q_i=\lceil\log_d r_i\rceil$ and $a_i=|F_i|+\sum_{j\in I_i}q_j$ (4.44). Given $G,\chi,d,\mathcal L$, Algorithm 2 learns every unknown $|\psi\rangle\in S_d(G,\chi)$ to trace-norm error at most $\epsilon\in(0,1]$ with success probability at least $1-\delta$, $\delta\in(0,1)$, using
--   $$
--   O\Big(\frac{L^3}{\epsilon^4}\Big(\max_{i\in[L]} r_i d^{a_i}+\log(L/\delta)\Big)\Big)\quad(4.73)
--   $$
--   copies, and in particular $O\big(\frac{L^3}{\epsilon^4}(d^{\mathrm{lc}_{d,\chi}(\mathcal L)}+\log(L/\delta))\big)$ copies (4.74). If a weight function $w:E\to\mathbb N$ is given and the input belongs to $S_d(G,w)$, the same algorithm with the weighted rank bounds $r_i=\prod_{e\in\mathrm{cut}_G(S_i)}w(e)$ (4.42) satisfies (4.73) with the weighted $r_i,a_i$, and uses $O\big(\frac{L^3}{\epsilon^4}(d^{\mathrm{lc}_{d,w}(\mathcal L)}+\log(L/\delta))\big)$ copies (4.75). The classical processing time is polynomial in $L$, $\max_i d^{a_i}$, $\max_i r_i$, $1/\epsilon$ and $\log(1/\delta)$.
--
--   This is the general realisable learner from which the path, tree, cutwidth and tree-cutwidth bounds follow.
--
--   **Formalization Note** One learner family on instances carrying an optional weight function, one absolute constant, and one polynomial-time printer of the circuit from the instance padded in unary with $n+L+\max_i d^{a_i}+\max_i r_i+\lceil1/\epsilon\rceil+\lceil\log_2(1/\delta)\rceil$ (with the weighted values in the weighted case).
--
--   Differences from the source:
--   - generalization: classical post-processing time polynomial in n, L, max_i d^{a_i}, max_i r_i, ⌈1/ε⌉, ⌈log₂(1/δ)⌉, assuming the tomography primitive and eigendecompositions run in polynomial time → unconditional: a polynomial-time printer of the learner's circuit from the instance padded in unary with n, L, max_i d^{a_i}, max_i r_i, ⌈1/ε⌉, ⌈log₂(1/δ)⌉; reason: the paper names the primitive (Lemma 3.9, pp.38, 59), which runs in polynomial time; the unconditional statement implies the conditional one
--   - encoding: O(·) bounds → one absolute constant C > 0 chosen before every instance parameter; reason: the base mission's reading of O(·); no constant depends on n, L, d, χ, w, k, ε or δ
--   - encoding: an algorithm receiving copies, ε and δ → one learner family (a Clifford+T circuit on qubit encodings of the copies plus ancillas, measured at the end) indexed by the instance with ⌈1/ε⌉ and ⌈log₂(1/δ)⌉; reason: the base mission's learner model; real ε ∈ (0, 1], δ ∈ (0, 1) remain the guarantee's parameters
--   - encoding: output a pure state with trace-norm error at most ε → the output decodes with the fixed decoder decodeTTN to a TTN whose normalised state is within trace norm ε of |ψ⟩⟨ψ|; reason: Gaussian-rational TTN entries cannot be exactly normalised; same guarantee
--   - reading: if a weight function is given, the same algorithm uses the weighted rank bounds → the learner's instance carries w as an option; with some w the bounds use r_i = ∏_{cut} w(e); reason: one algorithm for both cases
--   - encoding: q_i = ⌈log_d r_i⌉ → Nat.clog d r_i; reason: equal for r_i ≥ 1, d ≥ 2; for r_i = 0 the class S_d(G, w) is empty
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 4.8, Eqs. (4.73)–(4.75), pp.36–37

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_prob
import Definitions.Def_AgnosticTNS_CopyLearner_code
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_AgnosticTNS_Supplement_encRSeqIndex
import Definitions.Def_AgnosticTNS_Supplement_RealSuccess
import Definitions.Def_AgnosticTNS_Supplement_lcSeq
import Definitions.Def_AgnosticTNS_Supplement_rrW
import Definitions.Def_AgnosticTNS_rr
import Definitions.Def_AgnosticTNS_TNSchi
open Matrix
open QAlgorithms.Complexity

namespace AgnosticTNS.Supplement

/-- **Theorem 4.8 (Tomography using a learning sequence)**, pp.36–37 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)).
Let `G = ([n], E)` be a graph, `χ ≥ 1`, and `L = (S_i, I_i, F_i)_{i=1}^L` a learning sequence for `G`.
Given `G, χ, d, L`, Algorithm 2 learns any unknown `|ψ⟩ ∈ S_d(G, χ)` to trace-norm error at most `ϵ`
with success probability at least `1 − δ` using `O(L³/ϵ⁴ · (max_i r_i d^{a_i} + log(L/δ)))` copies
(4.73), with `r_i` from (4.41) and `a_i` from (4.44); in particular `O(L³/ϵ⁴ · (d^{lc_{d,χ}(L)} +
log(L/δ)))` copies (4.74). For a given `w : E → ℕ` and inputs in `S_d(G, w)`, the same algorithm with the
weighted rank bounds (4.42) satisfies (4.73) with the weighted `r_i, a_i`, and (4.75) with `lc_{d,w}(L)`.
The classical post-processing time is polynomial in `L`, `max_i d^{a_i}`, the largest rank parameter,
`1/ϵ`, and `log(1/δ)`.

**Formalization Note** One learner family on the instances `(n, G, L, d, χ, w?, ⌈1/ϵ⌉, ⌈log₂(1/δ)⌉)`
(`w = none`: uniform bounds), one absolute constant `C`, and one polynomial-time printer of the
Clifford+T circuit from the instance padded in unary with `n + L + max_i d^{a_i} + max_i r_i + ⌈1/ϵ⌉ +
⌈log₂(1/δ)⌉`. The paper's assumption that the tomography primitive and eigendecompositions run in
polynomial time is discharged (the primitive is Lemma 3.9, p.38), not kept as a hypothesis. Success is
`RealSuccess` (4.1): the decoded TTN's normalised state is within trace norm `ϵ` of `|ψ⟩⟨ψ|`. -/
theorem theorem_4_8 :
    ∃ (Lr : CopyLearner RSeqIndex (fun i => i.n) (fun i => i.d)) (C : ℝ) (g : Str → Str),
      0 < C ∧ PolyTimeComputable g ∧
      ∀ (n d χ : ℕ) (G : SimpleGraph (Fin n)) (Ls : LearningSequence n) (ε δ : ℝ),
        2 ≤ d → 1 ≤ χ → 0 < ε → ε ≤ 1 → 0 < δ → δ < 1 →
        (let i : RSeqIndex := ⟨n, G, Ls, d, χ, none, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩;
          g (encRSeqIndex i ++ unary (n + Ls.L + Finset.univ.sup (fun j => d ^ aR d Ls (rr G χ Ls) j) +
              Finset.univ.sup (rr G χ Ls) + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) = Lr.code i ∧
          (Lr.copies i : ℝ) ≤ C * (Ls.L : ℝ) ^ 3 / ε ^ 4 *
            (((Finset.univ.sup fun j => rr G χ Ls j * d ^ aR d Ls (rr G χ Ls) j : ℕ) : ℝ) +
              Real.log (Ls.L / δ)) ∧
          (Lr.copies i : ℝ) ≤ C * (Ls.L : ℝ) ^ 3 / ε ^ 4 *
            ((d : ℝ) ^ lcSeq d Ls (rr G χ Ls) + Real.log (Ls.L / δ)) ∧
          ∀ ψ ∈ TNSchi d G χ, 1 - δ ≤ Lr.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε)) ∧
        ∀ w : G.edgeSet → ℕ,
          let i : RSeqIndex := ⟨n, G, Ls, d, χ, some w, ⌈1 / ε⌉₊, ⌈Real.logb 2 (1 / δ)⌉₊⟩
          g (encRSeqIndex i ++ unary (n + Ls.L + Finset.univ.sup (fun j => d ^ aR d Ls (rrW G w Ls) j) +
              Finset.univ.sup (rrW G w Ls) + ⌈1 / ε⌉₊ + ⌈Real.logb 2 (1 / δ)⌉₊)) = Lr.code i ∧
          (Lr.copies i : ℝ) ≤ C * (Ls.L : ℝ) ^ 3 / ε ^ 4 *
            (((Finset.univ.sup fun j => rrW G w Ls j * d ^ aR d Ls (rrW G w Ls) j : ℕ) : ℝ) +
              Real.log (Ls.L / δ)) ∧
          (Lr.copies i : ℝ) ≤ C * (Ls.L : ℝ) ^ 3 / ε ^ 4 *
            ((d : ℝ) ^ lcSeq d Ls (rrW G w Ls) + Real.log (Ls.L / δ)) ∧
          ∀ ψ ∈ TNS d G w, 1 - δ ≤ Lr.prob i (vecMulVec ψ (star ψ)) (RealSuccess ψ ε) := by sorry

end AgnosticTNS.Supplement
