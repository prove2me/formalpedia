-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_of_deriv_growth_both_ends
-- name    : AvramDividend.Classical.cstar_finite_of_deriv_growth_both_ends
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T18:18:07.07133+00:00
-- url     : https://prove2.me/theorems/14bb551e-b9d2-4e23-bb34-6f4dda7b1661
-- title:
--   Existence of a finite optimal barrier when the scale derivative diverges at both positive-axis ends
-- statement:
--   For a scale-like W whose ordinary derivative is continuous on (0,∞), assume W'(x) tends to +∞ as x↓0 and as x→+∞. Then W' attains its global minimum at some strictly positive point, and the canonical optimal barrier cstar is finite. This theorem is especially relevant to the unbounded-variation non-Gaussian branch because it does not impose a finite one-sided derivative at zero and uses natural asymptotic growth rather than explicit near-zero and tail cutoffs.
-- source:
--   Use pinned Mathlib Tendsto.eventually_ge_atTop and mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset to select a positive near-zero threshold δ where W'(x)≥W'(a). Use eventually_atTop to select an upper threshold M>a where the same lower bound holds. Invoke previously authored cstar_finite_of_nearzero_and_tail_bounds to take a global positive derivative minimum on the intervening compact interval. All Lean validation must run remotely via Prove2Me.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set
open scoped Topology ENNReal

namespace AvramDividend.Classical
theorem cstar_finite_of_deriv_growth_both_ends
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hcont : ContinuousOn (deriv W) (Set.Ioi 0))
    (hzero : Filter.Tendsto (deriv W) (𝓝[>] (0 : ℝ)) Filter.atTop)
    (hinfty : Filter.Tendsto (deriv W) Filter.atTop Filter.atTop) :
    cstar W < ⊤ := by
  sorry
end AvramDividend.Classical
