-- Prove2me | Theorems.Thm_ErlerGross_B3_cubic_reciprocal_series_closed_form
-- name    : ErlerGross.B3_cubic_reciprocal_series_closed_form
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:06:10.157157+00:00
-- url     : https://prove2.me/theorems/d68b257b-4678-4675-bce3-01643ceed68b
-- title:
--   Cubic reciprocal series behind the (B.3) evaluation
-- statement:
--   The positive cubic reciprocal series obtained by simplifying the rational summand in Appendix B has the closed form $$sum_{nge 1}rac{1}{(2n-1)(3n-1)(3n-2)}=lnrac{27}{16}.$$ This is the elementary-series evaluation needed for the (B.3) closed form; the target series is its negative half term by term.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), Appendix B, p. 46, Eq. (B.3); cubic-denominator form follows by simplifying the displayed rational summand.

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem B3_cubic_reciprocal_series_closed_form :
    HasSum (fun n : Nat => 1 / (((2 * (n : Real) + 1) * (3 * (n : Real) + 1) * (3 * (n : Real) + 2))))
      (Real.log (27 / 16)) := by
  sorry

end ErlerGross
