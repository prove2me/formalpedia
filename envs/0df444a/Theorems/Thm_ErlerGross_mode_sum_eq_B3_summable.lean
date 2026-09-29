-- Prove2me | Theorems.Thm_ErlerGross_mode_sum_eq_B3_summable
-- name    : ErlerGross.mode_sum_eq_B3_summable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:03:10.242991+00:00
-- url     : https://prove2.me/theorems/b9e75c0d-4b8c-4c0d-b8c8-40ddf6ec472f
-- title:
--   Convergence of the scalar series in Eq. (B.3)
-- statement:
--   The scalar series on the right-hand side of Erler–Gross Eq. (B.3) converges:
--
--   \sum_{n\ge 1}\left(\frac{2}{2n-1}-\frac{1}{2n-\frac23}-\frac{1}{2n-\frac43}\right)
--
--   Here the  summand is ErlerGross.b3Term evaluated at $. This convergence assertion is the first component of the formalized Eq. (B.3) identity.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), Appendix B, eq. (B.3), p. 46

import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory
open ErlerGross

namespace ErlerGross
theorem mode_sum_eq_B3_summable :
    Summable (fun n : ℕ => b3Term (n + 1)) := by
  sorry
end ErlerGross
