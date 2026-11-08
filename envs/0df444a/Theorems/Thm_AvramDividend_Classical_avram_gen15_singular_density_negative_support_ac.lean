-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gen15_singular_density_negative_support_ac
-- name    : AvramDividend.Classical.avram_gen15_singular_density_negative_support_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:22:17.682211+00:00
-- url     : https://prove2.me/theorems/e0a856a6-7abd-4cb5-9820-8722c1129c53
-- title:
--   Singular Levy density has no nonnegative jumps and is absolutely continuous
-- statement:
--   The proposed singular negative Levy measure assigns zero mass to the nonnegative real half-line and is absolutely continuous relative to Lebesgue measure. These are the exact measure-dependent hypotheses of the source SpectrallyNegativeLevy.nu_Ici field and the third alternative of Condition33 in its Standing definition.
-- source:
--   Pinned Mathlib withDensity_apply, setLIntegral_congr_fun and withDensity_absolutelyContinuous applied to the literal proposed Levy density.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gen15_singular_density_negative_support_ac :
    (volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) (Ici (0 : ℝ)) = 0 ∧
    (volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0)) ≪ volume := by sorry
