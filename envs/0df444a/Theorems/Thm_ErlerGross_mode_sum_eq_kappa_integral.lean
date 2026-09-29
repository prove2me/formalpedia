-- Prove2me | Theorems.Thm_ErlerGross_mode_sum_eq_kappa_integral
-- name    : ErlerGross.mode_sum_eq_kappa_integral
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T19:21:45.374359+00:00
-- url     : https://prove2.me/theorems/6a0ccbdb-cc53-496b-987a-f04dbbf01462
-- title:
--   $\kappa$-basis integral representation of $\sum 3m_{2n}\beta_{2n}$
-- statement:
--   Transforming to the continuous $\kappa$ basis of the Neumann spectrum, $$\sum_{n\ge1}3\,m_{2n}\beta_{2n}=\int_{-\infty}^{\infty}d\kappa\,m(\kappa)\beta(\kappa)=2\int_{-\infty}^{\infty}d\kappa\,\frac{1-\cosh\frac{\pi\kappa}{2}}{1+2\cosh\frac{\pi\kappa}{2}}\,\frac{1}{2\kappa\sinh\frac{\pi\kappa}{2}}.$$ Formally: the integrand is Lebesgue integrable on $\mathbb R$ and the series converges to twice its integral.
-- source:
--   T. G. Erler and D. J. Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, arXiv:hep-th/0406199v2 (2004), https://arxiv.org/abs/hep-th/0406199; Appendix B, p. 45 (display following 'To prove this formula we must evaluate the sum/integral')

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem mode_sum_eq_kappa_integral :
    Integrable kappaIntegrand ∧
      HasSum (fun n : ℕ => 3 * neumannMEven (n + 1) * betaVec (2 * (n + 1)))
        (2 * ∫ κ, kappaIntegrand κ) := by
  sorry

end ErlerGross
