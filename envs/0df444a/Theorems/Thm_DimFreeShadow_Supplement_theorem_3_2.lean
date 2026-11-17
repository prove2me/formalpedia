-- Prove2me | Theorems.Thm_DimFreeShadow_Supplement_theorem_3_2
-- name    : DimFreeShadow.Supplement.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T07:02:01.828448+00:00
-- url     : https://prove2.me/theorems/5339e5a6-1242-4162-bd55-faa5a5e7249e
-- title:
--   Theorem 3.2 — failure $\tau$ with $r=\lceil\log_2(1/\tau)\rceil$, $n=\lceil18r^2/\eta^2\rceil$, and $rn=O((1+\log(1/\tau))^3/\eta^2)$
-- statement:
--   Fix a finite ensemble $\{(p_x,\rho_x):x\in\mathcal X\}$ of states on a finite-dimensional Hilbert space $\mathcal H$ ($p_x>0$, $\sum_xp_x=1$), one observable $0\preceq E\preceq I$, an accuracy $\eta\in(0,1]$ and a failure target $\tau\in(0,1)$. Set
--
--   $$
--   r:=\Big\lceil\log_2\frac1\tau\Big\rceil,\qquad n:=\Big\lceil\frac{18r^2}{\eta^2}\Big\rceil .
--   $$
--
--   **Theorem.**
--   1. The $r$-round sequential posterior PGM with $n$ copies per round, followed by a decoder $d_E:\mathcal X^r\to[0,1]$ as in Theorem 3.1, satisfies
--   $$
--   \Pr\big[|d_E(H_r)-\operatorname{Tr}(E\rho_X)|>\eta\big]\le\tau .
--   $$
--   2. The number of copies satisfies $T=rn=O\big((1+\log(1/\tau))^3/\eta^2\big)$: there is a universal constant $C$ with $rn\le C(1+\log(1/\tau))^3/\eta^2$ for all such $\tau,\eta$.
--
--   Together with a union bound over $M$ observables (Corollary 3.3) this gives the sequential PGM's $O(\log^3(M/\delta)/\epsilon^2)$ guarantee for a known finite prior.
--
--   **Formalization Note** The constant $C$ is chosen before the ensemble, $E$, $\eta$ and $\tau$; $r$ and $n$ are pinned to exactly the values above. The probability is computed from the joint law `seqPGMLaw`, as in Theorem 3.1. $\log_2$ is `Real.logb 2`, $\log$ is natural.
--
--   Differences from the source:
--   - encoding: a finite-dimensional Hilbert space H and its tensor powers → ℂ^d for a finite type d, with H^{⊗T} indexed by Fin T → d; reason: every finite-dimensional Hilbert space is unitarily equivalent to some ℂ^d; the same instances
--   - reading: followed by the decoder from Theorem 3.1 → there is a decoder d_E : X^r → [0, 1] with the stated failure bound; reason: Theorem 3.1 asserts only the existence of such a decoder, and its bound at these r, n is the source's proof
--   - encoding: T = rn = O((1 + log(1/τ))³/η²) → ∃ C, chosen before every other quantity, with rn ≤ C (1 + log(1/τ))³/η²; reason: the meaning of the O(·) with a universal constant
--   - encoding: Pr[|d_E(H_r) − Θ| > η] under Algorithm 1 → the sum of p_x ∏_s Tr(G^{(s)}_{y_s|h_{s−1}} ρ_x^{⊗n}) over the pairs (x, h) with |d_E(h) − θ_x| > η; reason: this is the law of (X, H_r) defined by Algorithm 1 and Eq. (12)
--   - encoding: the posterior at a zero-probability history is arbitrary → the posterior is left unchanged when p^h_y = 0; reason: the source allows any completion and the law does not depend on it
--   - encoding: Tr(·) of an effect times a state (a real number) → the real part .re of the complex trace; reason: the trace of a product of two positive semidefinite matrices is real; the same value
-- source:
--   Jeronimo, Huang, Liu, Dimension-Free Polylogarithmic Quantum Shadow Tomography, arXiv:2608.06345 (sha256 a1a42249…), Theorem 3.2 and Eq. (16), p.15

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_DimFreeShadow_Supplement_seqPGMLaw

namespace DimFreeShadow

namespace Supplement

/-- **Theorem 3.2 (iteration: failure `τ` with `T = O((1 + log(1/τ))³/η²)` copies)**
(arXiv:2608.06345, sha256 a1a42249…, Theorem 3.2 and Eq. (16), p.15). Fix a finite ensemble,
one observable `E`, an accuracy `η ∈ (0, 1]`, and a failure target `τ ∈ (0, 1)`. Set
`r := ⌈log₂(1/τ)⌉`, `n := ⌈18r²/η²⌉` (16). Then the r-round posterior-refocused PGM, followed
by the decoder from Theorem 3.1, satisfies `Pr[|d_E(H_r) − Tr(Eρ_X)| > η] ≤ τ`. Moreover,
`T = rn = O((1 + log(1/τ))³/η²)`.

**Formalization Note** `H = ℂ^d` for a finite type `d`; ensemble with `p_x > 0`, `Σ_x p_x = 1`,
density matrices `ρ_x`. "The decoder from Theorem 3.1" is a decoder `d_E : X^r → [0, 1]` whose
existence Theorem 3.1 asserts, so the first clause asserts such a decoder. The `O(·)` is a
universal constant `C`, chosen before the ensemble, `E`, `η` and `τ`. `r` and `n` are fixed to
exactly the values of (16) through the equations `r = ⌈log₂(1/τ)⌉₊`, `n = ⌈18r²/η²⌉₊`.
`log₂` is `Real.logb 2`; `log` is natural. Traces through real parts. -/
theorem theorem_3_2 :
    ∃ C : ℝ, ∀ (X d : Type) [Fintype X] [Fintype d] [DecidableEq d] (p : X → ℝ),
      (∀ x, 0 < p x) → ∑ x, p x = 1 → ∀ ρ : X → Matrix d d ℂ,
      (∀ x, WildeQIT.IsDensityOperator (ρ x)) → ∀ E : Matrix d d ℂ, QAlgorithms.IsEffect E →
      ∀ η τ : ℝ, 0 < η → η ≤ 1 → 0 < τ → τ < 1 →
      ∀ r n : ℕ, r = ⌈Real.logb 2 (1 / τ)⌉₊ → n = ⌈18 * (r : ℝ) ^ 2 / η ^ 2⌉₊ →
        (∃ dE : (Fin r → X) → ℝ, (∀ h, 0 ≤ dE h ∧ dE h ≤ 1) ∧
          ∑ x, ∑ h ∈ Finset.univ.filter
              (fun h : Fin r → X => η < |dE h - (E * ρ x).trace.re|),
            seqPGMLaw p ρ n r x h ≤ τ) ∧
        ((r * n : ℕ) : ℝ) ≤ C * (1 + Real.log (1 / τ)) ^ 3 / η ^ 2 := by sorry

end Supplement

end DimFreeShadow
