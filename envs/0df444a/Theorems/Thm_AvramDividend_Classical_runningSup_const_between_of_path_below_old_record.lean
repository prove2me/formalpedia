-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_const_between_of_path_below_old_record
-- name    : AvramDividend.Classical.runningSup_const_between_of_path_below_old_record
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T00:13:04.145403+00:00
-- url     : https://prove2.me/theorems/5b5f93de-1474-41f5-8b69-68db9efb2033
-- title:
--   Actual reflected Lévy running supremum remains constant on every interval without a new underlying record
-- statement:
--   Let X be the actual canonical spectrally negative Lévy process with running supremum S. On any time interval u≤v, if X(t)≤S(u) for every u≤t≤v, then S(v)=S(u). Prove the forward inequality by the accepted exact representation S(v)=sup_{0≤t≤v}X(t): times t≤u are bounded by S(u) using accepted pointwise domination and running-supremum monotonicity, while times t≥u are bounded by the supplied no-new-record hypothesis. The reverse inequality is the accepted monotonicity S(u)≤S(v). This is a necessary direct canonical step towards proving the record local time dS is carried by the contact set {S=X}, hence towards construction of the Itô excursion measure of R=S−X. It is not itself the full support theorem or sigma-finite excursion law.
-- source:
--   Accepted runningSup_monotone_and_path_le (848fbd48) and runningSup_eq_rawSup_nonneg (992246e6); Mathlib indexed supremum le.

import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Mathlib.Order.ConditionallyCompleteLattice.Indexed

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.runningSup_const_between_of_path_below_old_record
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u v : ℝ≥0) (huv : u ≤ v)
    (hBelow : ∀ t : ℝ≥0, u ≤ t → t ≤ v →
      X.X t ω ≤ runningSup X u ω) :
    runningSup X v ω = runningSup X u ω := by sorry
