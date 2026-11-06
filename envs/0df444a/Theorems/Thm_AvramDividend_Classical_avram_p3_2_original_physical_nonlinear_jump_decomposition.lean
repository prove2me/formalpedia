-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_physical_nonlinear_jump_decomposition
-- name    : AvramDividend.Classical.avram_p3_2_original_physical_nonlinear_jump_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:21:10.950542+00:00
-- url     : https://prove2.me/theorems/3f543d6e-b86c-44ab-9550-6b5023045c33
-- title:
--   Original controlled physical nonlinear jump splits into actual Lévy source and right dividend payment
-- statement:
--   At each positive physical time, the actual original controlled reserve's nonlinear w-jump equals the nonlinear Lévy-X source jump evaluated at the true pre-payment state plus the nonlinear right-dividend atom. Uses true cadlag X and D, preserving coincident jump timing and eliminating any assumed original left-limit witness.
-- source:
--   Pinned Proved cadlag X 09e1699b, original controlled prestate af64d023 and simultaneous nonlinear source split 2c18df8a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_controlled_left_prestate_explicit_source_eq
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_simultaneous_nonlinear_jump_split

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_physical_nonlinear_jump_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (ω : Ω) (t : ℝ≥0) (ht : 0 < t) :
    w (x + X.X t ω - rightLimit D t ω) -
      w (Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t) =
      (w (x + X.X t ω - D t ω) -
        w (x + Function.leftLim
          (fun s : ℝ≥0 => X.X s ω) t - D t ω)) +
      (w (x + X.X t ω - rightLimit D t ω) -
        w (x + X.X t ω - D t ω)) := by sorry
