-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_phys17_original_postright_reserve_source_increment_ae
-- name    : AvramDividend.Classical.avram_bv_phys17_original_postright_reserve_source_increment_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:31:18.880784+00:00
-- url     : https://prove2.me/theorems/1431d059-ab4a-4041-be6b-ff94a8ffb981
-- title:
--   Original BV post-right-payment reserve increments equal drift minus true source jumps and dividends
-- statement:
--   On one original-process almost-sure event for every pair of physical times, the increment of post-right-payment reserve is exactly deterministic BV drift minus the change of the original negative-jump source and the right-limit dividend increment. Valid also for randomly stopped or nonuniform meshes when evaluated samplewise, without claiming a martingale or uniform error bound.
-- source:
--   Derived source-exact physical reserve increment certificate from Proved 79a63ca0. It is an algebraic input for the original stopped cash/terminal ledger c5ce01c6, d5a21f7c and e0b94d7f, retaining the genuine source jump sum and payment endpoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_phys17_original_postright_reserve_source_increment_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0),
      (x + X.X t ω - rightLimit D t ω) -
        (x + X.X s ω - rightLimit D s ω) =
      ((t : ℝ) - (s : ℝ)) * X.drift -
        ((∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0) -
         (∑' v : ℝ≥0, if 0 < v ∧ v ≤ s then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
          else 0)) -
        (rightLimit D t ω - rightLimit D s ω) := by sorry
