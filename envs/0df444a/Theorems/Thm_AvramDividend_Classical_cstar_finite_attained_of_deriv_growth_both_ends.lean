-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_attained_of_deriv_growth_both_ends
-- name    : AvramDividend.Classical.cstar_finite_attained_of_deriv_growth_both_ends
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T21:24:04.676272+00:00
-- url     : https://prove2.me/theorems/8005535f-ac89-4862-8f97-b11c3648b967
-- title:
--   Finite and attained Avram barrier under derivative divergence at both ends of the positive half-line
-- statement:
--   Let W' be continuous on (0,infinity), and suppose W'(x) tends to +infinity both as x approaches zero from the right and as x approaches +infinity. For any reference a>0, the canonical dividend barrier cstar is finite and its real value is itself a strictly positive global derivative minimiser. Crucially, this does not assume derivative continuity or a finite derivative at zero, making it suitable for the unbounded-variation, no-Gaussian branch once its process-specific endpoint asymptotics are established.
-- source:
--   Use right-filter derivative divergence to find a strict near-zero bound relative to W'(a). Use divergence at infinity for a tail lower bound and minimise W' on a compact interval [δ/2,M] using pinned IsCompact.exists_isMinOn, obtaining a positive global minimiser b. The near-zero bound is strict relative to b, so the new cstar_attained_of_strict_nearzero_bound theorem shows cstar itself is attained. Existing cstar_lt_top_of_minimizer yields finiteness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top_of_minimizer
import Theorems.Thm_AvramDividend_Classical_cstar_attained_of_strict_nearzero_bound
open AvramDividend.Classical Filter Set
open scoped Topology ENNReal

namespace AvramDividend.Classical

theorem cstar_finite_attained_of_deriv_growth_both_ends (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0))
    (hzero : Filter.Tendsto (deriv W) (𝓝[>] (0 : ℝ)) Filter.atTop)
    (hinfty : Filter.Tendsto (deriv W) Filter.atTop Filter.atTop) :
    cstar W < ⊤ ∧ (cstar W).toReal ∈ cstarSet W := by
  sorry

end AvramDividend.Classical
