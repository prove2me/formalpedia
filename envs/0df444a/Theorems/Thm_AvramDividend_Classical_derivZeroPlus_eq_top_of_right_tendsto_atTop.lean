-- Prove2me | Theorems.Thm_AvramDividend_Classical_derivZeroPlus_eq_top_of_right_tendsto_atTop
-- name    : AvramDividend.Classical.derivZeroPlus_eq_top_of_right_tendsto_atTop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:11:19.028662+00:00
-- url     : https://prove2.me/theorems/f711aaad-1543-4cfd-ab1f-e14ce58f18ed
-- title:
--   Diverging ordinary scale derivative yields infinite extended zero-right derivative
-- statement:
--   When W'(y) diverges to positive infinity as y approaches zero from the right, its EReal one-sided liminf derivZeroPlus W is precisely +infinity. This supplies the analytic identification required by the source-faithful zero-barrier convention W(0)/∞=0, complementing the Proved finite-derivative identification lemma.
-- source:
--   Pinned Mathlib EReal.tendsto_coe_nhds_top_iff and Filter.Tendsto.liminf_eq; ScaleFunction.derivZeroPlus definition.

import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Instances.EReal.Lemmas
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical Filter Set

theorem AvramDividend.Classical.derivZeroPlus_eq_top_of_right_tendsto_atTop
    (W : ℝ → ℝ)
    (hderiv : Filter.Tendsto (fun y : ℝ => deriv W y)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop) :
    derivZeroPlus W = ⊤ := by sorry
