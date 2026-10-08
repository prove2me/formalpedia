-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_attained_of_pos_cstar_and_deriv_continuous
-- name    : AvramDividend.Classical.cstar_attained_of_pos_cstar_and_deriv_continuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:41:53.890974+00:00
-- url     : https://prove2.me/theorems/5414d234-1640-4741-b9a4-df557ad7a9e9
-- title:
--   Positive finite canonical dividend barrier is an attained derivative minimiser under positive-axis continuity
-- statement:
--   Suppose the derivative of W is continuous on (0,infinity) and has at least one positive global minimiser. If the real value of the infimum-defined canonical cstar is strictly positive, then cstar itself is an attained positive global derivative minimiser. This avoids ALL strict comparisons with either the ordinary derivative or one-sided derivative at zero. It follows because the cstar infimum bounds every positive minimiser away from zero, so the positive minimiser set is closed, and a compact initial interval yields its least element. This is a useful positive-cstar branch in the canonical Avram dichotomy.
-- source:
--   The ENNReal iInf defining cstar is below ENNReal.ofReal x for every positive global minimiser x. ENNReal.toReal_mono transfers this to (cstar W).toReal ≤ x. If cstar.toReal>0, no point of (0,cstar.toReal) can minimise the derivative, forcing a strict derivative gap there. Apply the source-faithful near-zero-gap closedness helper and the Prove2Me-Proved compact-initial-minimiser attainment theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped ENNReal

namespace AvramDividend.Classical

theorem cstar_attained_of_pos_cstar_and_deriv_continuous
    (W : ℝ → ℝ) (a : ℝ)
    (ha : a ∈ cstarSet W)
    (hcpos : 0 < (cstar W).toReal)
    (hcont : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ))) :
    (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
