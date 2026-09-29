-- Prove2me | Theorems.Thm_ErlerGross_kappa_integral_eq_residue_sum
-- name    : ErlerGross.kappa_integral_eq_residue_sum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:32:19.935739+00:00
-- url     : https://prove2.me/theorems/f80b372c-59d4-41ad-92d1-1810854662ad
-- title:
--   Residue evaluation of the $\kappa$-integral
-- statement:
--   Closing the contour in the upper half plane, the poles at $2i(2n-1)$, $2i(2n-\frac43)$, $2i(2n-\frac23)$ give $$\int_{-\infty}^{\infty}d\kappa\,\frac{1-\cosh\frac{\pi\kappa}{2}}{1+2\cosh\frac{\pi\kappa}{2}}\,\frac{1}{2\kappa\sinh\frac{\pi\kappa}{2}}=\sum_{n\ge1}\left[\frac{2}{2n-1}-\frac{1}{2n-\frac23}-\frac{1}{2n-\frac43}\right].$$
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix B, pp. 45-46 (residues at $2i(2n-1)$, $2i(2n-4/3)$, $2i(2n-2/3)$ leading to eq. B.3)

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem kappa_integral_eq_residue_sum :
    HasSum (fun n : ℕ => b3Term (n + 1)) (∫ κ, kappaIntegrand κ) := by
  sorry

end ErlerGross
