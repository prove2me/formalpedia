-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_abs_le_of_fderiv_bounded
-- name    : FiniteEnergyPlane.exists_abs_le_of_fderiv_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T22:19:58.443554+00:00
-- url     : https://prove2.me/theorems/a5160fca-8e1d-4c59-b1fc-2cbd35343011
-- title:
--   Uniform gradient bounds and a common zero give uniform bounds on compact sets
-- statement:
--   Let $U\subseteq\mathbb{C}$ be open and connected, and let $b_k:U\to\mathbb{R}$ be smooth functions with $b_k(z_0)=0$ for a common point $z_0\in U$. If $\sup_k\sup_{K}\|db_k\|<\infty$ for every compact $K\subseteq U$, then $\sup_k\sup_{K}|b_k|<\infty$ for every compact $K\subseteq U$.
--
--   This is the normalization step used to extract convergent subsequences of maps whose gradients are locally bounded.
--
--   **Formalization Note** Connectedness is `IsPreconnected U`, which suffices since $z_0\in U$. Smoothness is `ContDiffOn ℝ ∞ (b k) U`.
-- source:
--   Auxiliary to U. Hryniewicz, Trans. AMS 364 (2012), arXiv:0812.4076, Section 4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `U ⊆ ℂ` be open and preconnected and let `bₖ` be smooth real functions on `U` vanishing at a
common point `z₀ ∈ U`. If the derivatives of the `bₖ` are uniformly bounded on every compact subset of
`U`, then the `bₖ` themselves are uniformly bounded on every compact subset of `U`. -/
theorem exists_abs_le_of_fderiv_bounded (U : Set ℂ) (hU : IsOpen U) (hUc : IsPreconnected U)
    (b : ℕ → ℂ → ℝ) (hb : ∀ k, ContDiffOn ℝ ∞ (b k) U) (z₀ : ℂ) (hz₀ : z₀ ∈ U)
    (hb0 : ∀ k, b k z₀ = 0)
    (hgrad : ∀ Kc : Set ℂ, Kc ⊆ U → IsCompact Kc → ∃ M : ℝ, ∀ k, ∀ z ∈ Kc, ‖fderiv ℝ (b k) z‖ ≤ M)
    (Kc : Set ℂ) (hKc : Kc ⊆ U) (hKcc : IsCompact Kc) :
    ∃ A : ℝ, ∀ k, ∀ z ∈ Kc, |b k z| ≤ A := by
  sorry

end FiniteEnergyPlane
