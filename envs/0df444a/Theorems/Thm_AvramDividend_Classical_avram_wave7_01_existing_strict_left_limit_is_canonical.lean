-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_existing_strict_left_limit_is_canonical
-- name    : AvramDividend.Classical.avram_wave7_01_existing_strict_left_limit_is_canonical
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T19:16:41.280789+00:00
-- url     : https://prove2.me/theorems/904bf313-6fdc-461c-ab9d-b8fac48f60e0
-- title:
--   Every existing finite strict-left limit at positive time agrees with the canonical leftLim
-- statement:
--   At any strictly positive nonnegative time, an existing finite left-sided limit is equal to the canonical Function.leftLim, because the strict-left neighbourhood filter is nontrivial and the target is Hausdorff. This converts the exact path assumption of the canonical Borel extractor into the accepted two-sign jump-time enumeration interface.
-- source:
--   Mathlib nhdsLT_neBot_of_exists_lt and leftLim_eq_of_tendsto, as verified in the Proved source helper 60073045.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_existing_strict_left_limit_is_canonical
    (Y : ℝ≥0 → ℝ) (u : ℝ≥0) (hu : 0 < u)
    (hLeft : ∃ l : ℝ, Tendsto Y (𝓝[<] u) (𝓝 l)) :
    Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u)) := by sorry
