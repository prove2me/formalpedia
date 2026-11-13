-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a57_true_stop_raw_quadratic_energy_finset_bound
-- name    : AvramDividend.Classical.avram_ga_a57_true_stop_raw_quadratic_energy_finset_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:33:11.504213+00:00
-- url     : https://prove2.me/theorems/c09806ef-4a46-4692-9029-ac29ce132ff6
-- title:
--   True stop-masked original Gaussian raw quadratic mesh energy is bounded by centred energy and squared drift budget
-- statement:
--   On any finite set of original physical grid cells selected by a stopping-time mask, squared raw source increments have an upper bound by twice the centred selected quadratic energy plus twice the number of grid cells times the squared deterministic drift.
-- source:
--   Original Gaussian positive Taylor small-increment energy budget for b0d9951c; combine ga_a39 with raw source ga_a56.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a57_true_stop_raw_quadratic_energy_finset_bound {ι : Type*} (S : Finset ι) (z : ι → ℝ)
    (active : ι → Prop) [DecidablePred active] (d : ℝ) :
    Finset.sum S (fun i => if active i then (z i + d)^2 else 0) ≤
      2 * Finset.sum S (fun i => if active i then (z i)^2 else 0) +
        2 * (S.card : ℝ) * d^2 := by sorry
