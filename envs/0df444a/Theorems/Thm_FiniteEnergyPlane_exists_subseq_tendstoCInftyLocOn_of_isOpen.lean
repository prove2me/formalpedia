-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_subseq_tendstoCInftyLocOn_of_isOpen
-- name    : FiniteEnergyPlane.exists_subseq_tendstoCInftyLocOn_of_isOpen
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-25T22:05:16.772287+00:00
-- url     : https://prove2.me/theorems/cea3404c-68ba-4c29-a842-a93ad3d696b5
-- title:
--   Compactness in C^∞_loc of pseudoholomorphic maps on an open subset of the plane
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $O\subset E$ open, and $J$ a smooth almost complex structure on $O$. Let $U\subset\mathbb C$ be open and let $v_k:U\to E$ be smooth $J$-holomorphic maps such that for every compact $K\subset U$ there are a compact $K'\subset O$ and $M$ with $v_k(K)\subset K'$ and $\|Dv_k\|\le M$ on $K$ for all $k$. Then a subsequence $v_{k_j}$ converges in $C^\infty_{\mathrm{loc}}(U)$ to a smooth $J$-holomorphic map $w:U\to O$.
--
--   **Formalization Note** "$J$ smooth almost complex structure on $O$" is `JHolomorphic.IsAlmostComplexOn J O` (it includes that $O$ is open). $C^\infty_{\mathrm{loc}}(U)$ convergence is `JHolomorphic.TendstoCInftyLocOn`: uniform convergence of every `iteratedFDeriv` on every compact subset of $U$. The maps are functions on all of $\mathbb C$; only their behaviour on $U$ matters.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Proposition 9.1 (open-set form)

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `C^∞_loc` compactness of pseudoholomorphic maps on an open subset of `ℂ` (Wendl,
Lectures on SFT, Prop. 9.1, open-set form). Let `J` be a smooth almost complex structure on an
open set `O` of a finite-dimensional space `E`, `U ⊆ ℂ` open, and `v_k : U → E` smooth
`J`-holomorphic maps such that on every compact `K ⊆ U` the images `v_k(K)` lie in a fixed
compact subset of `O` and `|Dv_k|` is bounded uniformly in `k`. Then a subsequence converges in
`C^∞_loc(U)` to a smooth `J`-holomorphic map `w : U → O`. -/
theorem exists_subseq_tendstoCInftyLocOn_of_isOpen {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (U : Set ℂ) (hU : IsOpen U) (v : ℕ → ℂ → E)
    (hv : ∀ k, ContDiffOn ℝ ∞ (v k) U) (hhol : ∀ k, JHolomorphic.IsJHolomorphicOn J U (v k))
    (hbd : ∀ K ⊆ U, IsCompact K → ∃ K' : Set E, IsCompact K' ∧ K' ⊆ O ∧ ∃ M : ℝ,
      ∀ k, ∀ z ∈ K, v k z ∈ K' ∧ ‖fderiv ℝ (v k) z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ w : ℂ → E, ContDiffOn ℝ ∞ w U ∧
      JHolomorphic.IsJHolomorphicOn J U w ∧ Set.MapsTo w U O ∧
      JHolomorphic.TendstoCInftyLocOn (fun j => v (φ j)) w U := by
  sorry

end FiniteEnergyPlane
