-- Prove2me | Theorems.Thm_CauchyRiemannIndex_eq_of_continuous_periodic_ae_eq
-- name    : CauchyRiemannIndex.eq_of_continuous_periodic_ae_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-09T16:38:19.180415+00:00
-- url     : https://prove2.me/theorems/13f4e722-1e9c-4ab2-b766-4fbc2d816ef2
-- title:
--   Continuous t-periodic maps equal almost everywhere on the strip are equal
-- statement:
--   Let $E$ be a Hausdorff space and $g, h : \mathbb{R}\times\mathbb{R} \to E$ continuous and $1$-periodic in the second variable. If $g = h$ almost everywhere for Lebesgue measure on the strip $\mathbb{R}\times[0,1)$ (`cylMeasure`), then $g = h$ everywhere.
--
--   **Role.** Uniqueness of continuous representatives of classes in $L^p(\mathbb{R}\times S^1)$.
-- source:
--   Standard Sobolev embedding on the cylinder; setting of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry (arXiv:1011.1690), Ch. 4

import Definitions.Def_CauchyRiemannIndex_Setting

namespace CauchyRiemannIndex

open MeasureTheory

/-- Two continuous maps on `ℝ × ℝ`, `1`-periodic in `t`, that agree `cylMeasure`-almost everywhere
are equal. -/
theorem eq_of_continuous_periodic_ae_eq {E : Type*} [TopologicalSpace E] [T2Space E]
    {g h : ℝ × ℝ → E} (hg : Continuous g) (hh : Continuous h)
    (hgp : ∀ s t, g (s, t + 1) = g (s, t)) (hhp : ∀ s t, h (s, t + 1) = h (s, t))
    (hae : g =ᵐ[cylMeasure] h) : g = h := by
  sorry

end CauchyRiemannIndex
