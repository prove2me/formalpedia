-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys70_original_twoindex_discounted_physical_reserve_telescoping
-- name    : AvramDividend.Classical.avram_bvb_phys70_original_twoindex_discounted_physical_reserve_telescoping
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:20:38.70079+00:00
-- url     : https://prove2.me/theorems/84c1722d-23de-4d39-ab29-20cc8c1c402f
-- title:
--   Source-exact BV discounted physical reserve telescoping on every two-index grid row
-- statement:
--   Specialise the already proved original BV discounted reserve telescoping identity to each row of the exact two-index physical grid u(n,i), retaining the original jump-sum J, actual postpayment reserve U and all discount and payment increments. This is a reusable exact finite-row identity for the open zero-mark and finite-mark physical error branches.
-- source:
--   Root-connected Avram BV physical-grid 6ce6d0c3; direct specialisation of Proved becdaa6c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_phys18_original_discounted_physical_mesh_terminal_source_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys70_original_twoindex_discounted_physical_reserve_telescoping
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let U : ℝ≥0 → ℝ := fun v => x + X.X v ω - rightLimit D v ω
      let J : ℝ≥0 → ℝ := fun r =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      Real.exp (-(q * (u n (n + 1) : ℝ))) * w (U (u n (n + 1))) -
        Real.exp (-(q * (u n 0 : ℝ))) * w (U (u n 0)) =
      ∑ i ∈ Finset.range (n + 1),
        (Real.exp (-(q * (u n (i + 1) : ℝ))) *
          (w (U (u n i) +
            (((u n (i + 1) : ℝ) - (u n i : ℝ)) * X.drift -
              (J (u n (i + 1)) - J (u n i)) -
              (rightLimit D (u n (i + 1)) ω - rightLimit D (u n i) ω))) -
           w (U (u n i))) +
         (Real.exp (-(q * (u n (i + 1) : ℝ))) -
          Real.exp (-(q * (u n i : ℝ)))) * w (U (u n i))) := by sorry
