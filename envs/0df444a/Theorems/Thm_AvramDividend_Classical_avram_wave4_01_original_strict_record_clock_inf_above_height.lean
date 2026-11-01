-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_01_original_strict_record_clock_inf_above_height
-- name    : AvramDividend.Classical.avram_wave4_01_original_strict_record_clock_inf_above_height
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:23:04.469007+00:00
-- url     : https://prove2.me/theorems/945d7bf3-2561-4867-8171-9af88e457a2e
-- title:
--   Actual strict upper first-record time equals the infimum of first-record times at all strictly higher heights
-- statement:
--   For every original Lévy sample path and every real record height h, the first strict upward passage time T_h equals the infimum of T_r over all real r>h. The strict threshold definition gives the set identity {t: X_t>h}=union_{r>h}{t:X_t>r}: each witness X_t>h admits the midpoint r=(h+X_t)/2 with h<r<X_t. The other inequality follows from source threshold monotonicity. This is the exact deterministic right-order-continuity interface needed for measurable rational approximations and authentic source record-height Tonelli, with no sample path continuity assumption and no Standing.
-- source:
--   Canonical definition of twoSidedExitUpTime as nested iInf of strict crossing witnesses; Proved source monotonicity UUID 5060f2c9-5c3e-48d5-a44c-101f9a63f35a; Mathlib iInf_le_of_le and midpoint linear arithmetic. Distinct from mere threshold monotonicity and from any Esscher excursion theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_wave4_01_original_strict_record_clock_inf_above_height
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (h : ℝ) (ω : Ω) :
    twoSidedExitUpTime X h ω =
      ⨅ r : {r : ℝ // h < r}, twoSidedExitUpTime X r.1 ω := by sorry
