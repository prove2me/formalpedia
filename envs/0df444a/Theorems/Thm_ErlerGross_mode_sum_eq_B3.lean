-- Prove2me | Theorems.Thm_ErlerGross_mode_sum_eq_B3
-- name    : ErlerGross.mode_sum_eq_B3
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:33:54.49518+00:00
-- url     : https://prove2.me/theorems/611613d4-a758-4aa6-af16-399ed226aaf0
-- title:
--   Eq. (B.3): $\sum 3m_{2n}\beta_{2n}=2\sum\left[\frac{2}{2n-1}-\frac{1}{2n-2/3}-\frac{1}{2n-4/3}\right]$
-- statement:
--   Eq. (B.3): $$\sum_{n\ge1}3\,m_{2n}\beta_{2n}=2\sum_{n\ge1}\left[\frac{2}{2n-1}-\frac{1}{2n-\frac23}-\frac{1}{2n-\frac43}\right],$$ with both series convergent.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix B, eq. (B.3), p. 46

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem mode_sum_eq_B3 :
    Summable (fun n : ℕ => b3Term (n + 1)) ∧
      HasSum (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
        (2 * ∑' n : ℕ, b3Term (n + 1)) := by
  sorry

end ErlerGross
