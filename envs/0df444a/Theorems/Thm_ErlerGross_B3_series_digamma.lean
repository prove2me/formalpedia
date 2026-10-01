-- Prove2me | Theorems.Thm_ErlerGross_B3_series_digamma
-- name    : ErlerGross.B3_series_digamma
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T12:31:45.346353+00:00
-- url     : https://prove2.me/theorems/be529892-150d-4cbd-b72e-2507c34f67e1
-- title:
--   The Erler–Gross B.3 series in digamma form
-- statement:
--   The series of rational terms in Erler and Gross equation (B.3), written using the digamma function, has the value $$\frac{1}{2}\psi(2/3)+\frac{1}{2}\psi(1/3)-\psi(1/2).$$
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2, Appendix B, equation (B.3), together with the digamma series identity.

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem B3_series_digamma :
    HasSum (fun n : ℕ => ((b3Term (n + 1) : ℝ) : ℂ))
      (Complex.digamma ((2 : ℂ) / 3) / 2 + Complex.digamma ((1 : ℂ) / 3) / 2 -
        Complex.digamma ((1 : ℂ) / 2)) := by
  sorry

end ErlerGross
