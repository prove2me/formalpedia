-- Prove2me | Theorems.Thm_ErlerGross_sum_inv_n_two_n_add_one
-- name    : ErlerGross.sum_inv_n_two_n_add_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:36:54.091985+00:00
-- url     : https://prove2.me/theorems/2fde15bc-d6f0-4268-abec-747d09cbc0d0
-- title:
--   $\sum_{n\ge1}\frac{1}{n(2n+1)}=2-2\ln2$
-- statement:
--   $$\sum_{n\ge1}\frac{1}{n(2n+1)}=2-2\ln 2.$$ **Correction note:** the source prints the value as $2-\ln 2$, which is a misprint: the series equals $\approx0.6137=2-2\ln2$, whereas $2-\ln2\approx1.307$ (already the partial sums are bounded by $\sum 1/(2n^2)=\pi^2/12<1.307$). The corrected value is formalized.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix B, p. 46, first of the two auxiliary series formulas (printed there as '= 2 − ln 2', corrected here)

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem sum_inv_n_two_n_add_one :
    HasSum (fun n : ℕ => 1 / (((n : ℝ) + 1) * (2 * ((n : ℝ) + 1) + 1)))
      (2 - 2 * Real.log 2) := by
  sorry

end ErlerGross
