-- Prove2me | Theorems.Thm_ErlerGross_B3_series_closed_form
-- name    : ErlerGross.B3_series_closed_form
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:56:46.073697+00:00
-- url     : https://prove2.me/theorems/40d9f092-966d-4cec-acb4-67f6aaee56bb
-- title:
--   Closed form of the (B.3) series: $2\sum b_n=-\ln\frac{27}{16}$
-- statement:
--   $$\sum_{n\ge1}\left[\frac{2}{2n-1}-\frac{1}{2n-\frac23}-\frac{1}{2n-\frac43}\right]=-\frac12\ln\frac{27}{16},$$ i.e. the right side of (B.3) equals $-\ln\frac{27}{16}$.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix B, p. 46 ('Writing eq. B.3 in terms of these summations, we find $3m_{2n}\beta_{2n}=-\ln\frac{27}{16}$')

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem B3_series_closed_form :
    HasSum (fun n : ℕ => b3Term (n + 1)) (-Real.log (27 / 16) / 2) := by
  sorry

end ErlerGross
