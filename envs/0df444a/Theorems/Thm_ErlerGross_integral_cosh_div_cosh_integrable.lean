-- Prove2me | Theorems.Thm_ErlerGross_integral_cosh_div_cosh_integrable
-- name    : ErlerGross.integral_cosh_div_cosh_integrable
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-09-26T10:10:14.406441+00:00
-- url     : https://prove2.me/theorems/aaddbb23-37bb-4ae2-bcdf-ac2667300e99
-- title:
--   Integrability of the cosh quotient on the positive half-line
-- statement:
--   Let $a,b\in\mathbb C$ satisfy $|\operatorname{Re}a|<\operatorname{Re}b$. Then the function $x\mapsto\cosh(ax)/\cosh(bx)$ is integrable on the positive half-line:
--
--   $$
--   \int_0^\infty \left|\frac{\cosh(ax)}{\cosh(bx)}\right|\,dx<\infty.
--   $$
--
--   This is the convergence assertion needed before evaluating the complex integral in Appendix B.
--
--   **Formalization Note** Lean states this as `IntegrableOn` for a complex-valued function on `Set.Ioi 0`.
-- source:
--   Erler and Gross, Locality, Causality, and an Initial Value Formulation for Open String Field Theory, https://arxiv.org/abs/hep-th/0406199, Appendix B, p. 45.

import Mathlib
import Definitions.Def_ErlerGross_defs
open Real Filter Topology MeasureTheory

namespace ErlerGross

theorem integral_cosh_div_cosh_integrable (a b : ℂ) (hab : |a.re| < b.re) :
    IntegrableOn (fun x : ℝ => Complex.cosh (a * x) / Complex.cosh (b * x))
      (Set.Ioi 0) := by
  sorry

end ErlerGross
