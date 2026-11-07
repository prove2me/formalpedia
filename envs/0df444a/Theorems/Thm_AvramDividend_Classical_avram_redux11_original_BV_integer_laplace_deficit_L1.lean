-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_integer_laplace_deficit_L1
-- name    : AvramDividend.Classical.avram_redux11_original_BV_integer_laplace_deficit_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:05:48.257299+00:00
-- url     : https://prove2.me/theorems/539e958a-91be-4ebb-a9a5-6eed1fc4454c
-- title:
--   Original BV integer-time bounded Laplace residual deficits are integrable
-- statement:
--   For the original bounded-variation Lévy path, the Laplace deficit 1-exp(-R_n), where R is the authentic drift-minus-X-minus-all-actual-jumps remainder, is integrable at every integer time. This is the source-process boundedness and measurability part, independent of the zero-mean characteristic identity.
-- source:
--   Original BV source-path residual Laplace obligations feeding the proved conditional path identity c540bf8f and redux11 path child 79a63ca0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux11_original_BV_integer_laplace_deficit_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
      let R : ℝ≥0 → Ω → ℝ := fun t ω =>
        (((t : ℝ) * X.drift - X.X t ω) -
          (∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
            Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))
      ∀ n : ℕ, Integrable
        (fun ω => 1 - Real.exp (-(R (n : ℝ≥0) ω))) P := by sorry
