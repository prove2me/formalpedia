-- Prove2me | Theorems.Thm_AcycTesting_NearLinear_lemma_6_3
-- name    : AcycTesting.NearLinear.lemma_6_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:36:42.841247+00:00
-- url     : https://prove2.me/theorems/cbdad11d-5e45-4a2d-ab5d-034e6c460765
-- title:
--   Lemma 6.3 — positivity, ratio bound 1/4 and logarithmic-derivative bound 2^{|I|} for signed partition functions
-- statement:
--   Let $p=S^2/N$ and $\kappa=cp\le 1/(16e^2)$, and let $w=(w_I)$ be reals indexed by the subsets $I\subseteq[c]$ with $|I|\ge2$ such that $|w_I|\le |I|^{|I|-2}p^{|I|-1}$ for all such $I$. Let $\Phi_J(w)=\sum_{\mathcal C}\prod_{I\in\mathcal C}w_I$ over collections $\mathcal C$ of pairwise disjoint subsets of $J$ of size at least two. Then:
--   1. $\Phi_J(w)>0$ for every $J\subseteq[c]$;
--   2. $\big|\Phi_J(w)/\Phi_{J\setminus\{x\}}(w)-1\big|\le\frac14$ for every $J$ and $x\in J$;
--   3. for every $I$ with $|I|\ge2$,
--   $$0<\frac{\partial\log\Phi_{[c]}(w)}{\partial w_I}=\frac{\Phi_{[c]\setminus I}(w)}{\Phi_{[c]}(w)}\le 2^{|I|}.\tag{6.5}$$
--   The derivative is that of $t\mapsto\log\Phi_{[c]}(w')$ at $t=w_I$, where $w'$ agrees with $w$ except $w'_I=t$. Integrating (6.5) along an interpolation of activities gives the logarithmic comparison of Theorem 5.2.
--
--   Differences from the source:
--   - encoding: [c], weights w_I for I ⊆ [c] with |I| ≥ 2 → Fin c; w : Finset (Fin c) → ℝ whose values on sets with |I| < 2 are never used (Φ only uses sets of size ≥ 2); reason: Lean convention; the same functions
--   - encoding: p = S²/N → S real, N natural with 0 < N, p := S²/N; reason: p is undefined at N = 0; S need not be an integer
--   - encoding: ∂ log Φ[c](w)/∂wI → HasDerivAt of t ↦ log Φ_univ(Function.update w I t) at w I with value Φ_{univ \ I}(w)/Φ_univ(w); reason: the partial derivative in the coordinate w_I
--   - encoding: "for every I" in (6.5) → every I : Finset (Fin c) with 2 ≤ |I|; reason: w_I exists only for |I| ≥ 2
-- source:
--   Czumaj, Peng, Wang, Near-Linear Lower Bounds for Testing Directed Acyclicity, arXiv:2611.04901v1 (sha256 5685fc7b…), p. 26 (PDF 29), Lemma 6.3

import Mathlib
import Definitions.Def_AcycTesting_NearLinear_PermCores
import Definitions.Def_AcycTesting_NearLinear_Forests

namespace AcycTesting.NearLinear

/-- Lemma 6.3 (positivity and logarithmic derivatives) for `p = S²/N`, `κ = cp ≤ 1/(16e²)`. -/
theorem lemma_6_3 (c : ℕ) (S : ℝ) (N : ℕ) (hN : 0 < N)
    (hκ : (c : ℝ) * (S ^ 2 / N) ≤ 1 / (16 * Real.exp 1 ^ 2))
    (w : Finset (Fin c) → ℝ)
    (hw : ∀ I : Finset (Fin c), 2 ≤ I.card →
      |w I| ≤ (I.card : ℝ) ^ (I.card - 2) * (S ^ 2 / N) ^ (I.card - 1)) :
    (∀ J : Finset (Fin c), 0 < signedPartition w J) ∧
      (∀ J : Finset (Fin c), ∀ x ∈ J,
        |signedPartition w J / signedPartition w (J.erase x) - 1| ≤ 1 / 4) ∧
      (∀ I : Finset (Fin c), 2 ≤ I.card →
        HasDerivAt (fun t : ℝ => Real.log (signedPartition (Function.update w I t) Finset.univ))
            (signedPartition w (Finset.univ \ I) / signedPartition w Finset.univ) (w I) ∧
          0 < signedPartition w (Finset.univ \ I) / signedPartition w Finset.univ ∧
          signedPartition w (Finset.univ \ I) / signedPartition w Finset.univ ≤
            (2 : ℝ) ^ I.card) := by sorry

end AcycTesting.NearLinear
