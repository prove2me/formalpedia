-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_min_of_accumulated_minimizers
-- name    : AvramDividend.Classical.derivZeroPlus_eq_min_of_accumulated_minimizers
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:58:16.861513+00:00
-- url     : https://prove2.me/theorems/8eba74fd-ec08-4637-b649-5ab45652fc24
-- title:
--   The zero-boundary derivative liminf equals the minimum when global derivative minimisers accumulate at zero
-- statement:
--   Let S be the nonempty set of positive global minimisers of the real derivative W'. Suppose the real infimum of S is zero. Every a in S has the same globally minimal derivative value d. There are minimisers arbitrarily close to zero, making W'(x)=d frequently along the right-neighbourhood filter at zero; hence the right derivative liminf is at most d. As every positive derivative is at least d, it is also at least d. Thus the EReal right liminf at zero equals the finite real d, with no continuity or differentiability hypotheses besides the derivative values used in S. This closes the subtle zero-barrier, positive-minimiser-set branch needed for Proposition 3(i).
-- source:
--   Definitions cstarSet and derivZeroPlus; Mathlib csInf_mem_closure, mem_closure_iff_frequently, frequently_nhdsWithin_iff, Filter.liminf_le_of_frequently_le; Proved AvramDividend.Classical.deriv_global_lower_le_right_liminf.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical Filter Set Topology
open scoped ENNReal

theorem AvramDividend.Classical.derivZeroPlus_eq_min_of_accumulated_minimizers
    (W : ℝ → ℝ)
    (hS : (cstarSet W).Nonempty)
    (hzero : sInf (cstarSet W) = 0)
    (a : ℝ) (ha : a ∈ cstarSet W) :
    derivZeroPlus W = ((deriv W a : ℝ) : EReal) := by sorry
