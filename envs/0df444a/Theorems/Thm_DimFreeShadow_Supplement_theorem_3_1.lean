-- Prove2me | Theorems.Thm_DimFreeShadow_Supplement_theorem_3_1
-- name    : DimFreeShadow.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:01:11.565784+00:00
-- url     : https://prove2.me/theorems/fa8f38c4-0501-4d99-98e0-4cc4b6351aaa
-- title:
--   Theorem 3.1 — one-observable localization, $\Pr[|d_E(H_r)-\Theta|>\eta]\le(9r^2/(n\eta^2))^r$
-- statement:
--   Let $\mathcal E=\{(p_x,\rho_x):x\in\mathcal X\}$ be a finite ensemble of states on a finite-dimensional Hilbert space $\mathcal H$ ($p_x>0$, $\sum_xp_x=1$), let $0\preceq E\preceq I$ be an observable, and write $\theta_x=\operatorname{Tr}(E\rho_x)$ and $\Theta=\theta_X$. Run the $r$-round sequential posterior PGM (Algorithm 1) with $n$ copies per round, producing the full history $H_r\in\mathcal X^r$.
--
--   **Theorem.** For all integers $r,n\ge1$ and every $\eta\in(0,1]$ there is a deterministic decoder $d_E:\mathcal X^r\to[0,1]$ such that
--
--   $$
--   \Pr\big[|d_E(H_r)-\Theta|>\eta\big]\ \le\ \Big(\frac{9r^2}{n\eta^2}\Big)^{r}.
--   $$
--
--   The physical measurement is independent of $E$; only the classical decoder depends on it.
--
--   This is the paper's posterior-localization bound: the failure probability of one sequential PGM decays like a power $r$ of $r^2/(n\eta^2)$, which Theorem 3.2 turns into a high-confidence estimate.
--
--   **Formalization Note** The probability is the sum of the joint law $\Pr[X=x,H_r=h]$ (definition `seqPGMLaw`) over the pairs with $|d_E(h)-\theta_x|>\eta$. The law takes no observable as input, which is how the independence of the measurement from $E$ is expressed.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - encoding: Pr[|d_E(H_r) − Θ| > η] under Algorithm 1 → the sum of p_x ∏_s Tr(G^{(s)}_{y_s|h_{s−1}} ρ_x^{⊗n}) over the pairs (x, h) with |d_E(h) − θ_x| > η; reason: this is the law of (X, H_r) defined by Algorithm 1 and Eq. (12)
--   - encoding: the posterior at a zero-probability history is arbitrary → the posterior is left unchanged when p^h_y = 0; reason: the source allows any completion and the law does not depend on it
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Theorem 3.1, p.13; Algorithm 1, p.7; §3.1, p.12

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_Supplement_seqPGMLaw

namespace DimFreeShadow

namespace Supplement

/-- **Theorem 3.1 (one-observable localization)** (arXiv:2608.06345, sha256 a1a42249…,
Theorem 3.1, p.13). For every finite ensemble `{(p_x, ρ_x) : x ∈ X}`, every observable
`0 ⪯ E ⪯ I`, all integers `r, n ≥ 1`, and every `η ∈ (0, 1]`, there is a deterministic decoder
`d_E : X^r → [0, 1]` such that the r-round posterior-refocused PGM (Algorithm 1) satisfies
`Pr[|d_E(H_r) − Θ| > η] ≤ (9r²/(nη²))^r`, where `θ_x = Tr(Eρ_x)` and `Θ = θ_X`.
The physical measurement is independent of `E`.

**Formalization Note** `H = ℂ^d` for a finite type `d`; the ensemble has `p_x > 0`,
`Σ_x p_x = 1`, each `ρ_x` a density matrix. `X^r` is `Fin r → X`. The probability is the sum of
the joint law `seqPGMLaw p ρ n r x h = Pr[X = x, H_r = h]` over the pairs `(x, h)` with
`|d_E(h) − θ_x| > η`. `seqPGMLaw` does not take `E` (the measurement is independent of `E`);
only `d_E` depends on it. Traces through real parts. -/
theorem theorem_3_1 {X d : Type} [Fintype X] [Fintype d] [DecidableEq d] (p : X → ℝ)
    (hp : ∀ x, 0 < p x) (hp1 : ∑ x, p x = 1) (ρ : X → Matrix d d ℂ)
    (hρ : ∀ x, WildeQIT.IsDensityOperator (ρ x)) (E : Matrix d d ℂ)
    (hE : QAlgorithms.IsEffect E) (r n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) (η : ℝ) (hη0 : 0 < η)
    (hη1 : η ≤ 1) :
    ∃ dE : (Fin r → X) → ℝ, (∀ h, 0 ≤ dE h ∧ dE h ≤ 1) ∧
      ∑ x, ∑ h ∈ Finset.univ.filter (fun h : Fin r → X => η < |dE h - (E * ρ x).trace.re|),
          seqPGMLaw p ρ n r x h ≤ (9 * (r : ℝ) ^ 2 / ((n : ℝ) * η ^ 2)) ^ r := by sorry

end Supplement

end DimFreeShadow
