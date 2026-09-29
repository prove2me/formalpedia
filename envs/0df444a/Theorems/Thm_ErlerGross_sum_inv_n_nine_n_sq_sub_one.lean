-- Prove2me | Theorems.Thm_ErlerGross_sum_inv_n_nine_n_sq_sub_one
-- name    : ErlerGross.sum_inv_n_nine_n_sq_sub_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:44:21.160987+00:00
-- url     : https://prove2.me/theorems/184d6b36-1be5-4c46-8fc5-9e261d6d9ed2
-- title:
--   $\sum_{n\ge1}\frac{1}{n(9n^2-1)}=\frac32(\ln3-1)$
-- statement:
--   $$\sum_{n\ge1}\frac{1}{n(9n^2-1)}=\frac32(\ln3-1).$$
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix B, p. 46, second of the two auxiliary series formulas

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem sum_inv_n_nine_n_sq_sub_one :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * (9 * ((n : ℝ) + 1) ^ 2 - 1)))
      (3 / 2 * (Real.log 3 - 1)) := by
  sorry

end ErlerGross
