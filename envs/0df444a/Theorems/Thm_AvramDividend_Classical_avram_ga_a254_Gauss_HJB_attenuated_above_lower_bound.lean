-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a254_Gauss_HJB_attenuated_above_lower_bound
-- name    : AvramDividend.Classical.avram_ga_a254_Gauss_HJB_attenuated_above_lower_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:45:19.8079+00:00
-- url     : https://prove2.me/theorems/18cbf904-d986-470f-8278-0117d453d7cf
-- title:
--   Attenuated weighted HJB derivative retains a uniform lower bound in terms of its value at the right endpoint.
-- statement:
--   Attenuated weighted HJB derivative retains a uniform lower bound in terms of its value at the right endpoint. Source step in the original Gaussian HJB near-zero one-sided upper control, used with a249/a250/a251.
-- source:
--   Source-exact zero-jump Gaussian HJB origin weighted derivative comparison

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a254_Gauss_HJB_attenuated_above_lower_bound
    (g0 g e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hga : g0 ≤ g) : -|g0| ≤ e*g := by sorry
