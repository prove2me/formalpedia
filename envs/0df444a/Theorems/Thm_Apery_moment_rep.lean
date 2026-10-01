-- Prove2me | Theorems.Thm_Apery_moment_rep
-- name    : Apery.moment_rep
-- status  : Open
-- author  : @tomasz
-- created : 2026-10-01T10:56:49.715985+00:00
-- url     : https://prove2.me/theorems/01f33564-aa3f-452d-a4c9-7c244c6f83c8
-- title:
--   Positive-weight moment representation of the rational functional
-- statement:
--   For every natural number $K$ and every rational polynomial $P$, the function $J_{K,P}(y)=P(y^2)w(y)/D_K(y^2)$ is Lebesgue integrable on $(0,\infty)$ and
--   $$\mu_{z_5}(P/D_K)=\int_0^\infty\frac{P(y^2)}{D_K(y^2)}w(y)\,dy.$$
--   There is no degree restriction on $P$, and $K=0$ is included. Integrability is part of the conclusion. This is the functional identity linking the rational-polynomial construction to the analytic estimates.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Positivity.lean#L85-L110

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceValue
import Definitions.Def_Zeta5_MomentWeight

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem moment_rep (K : ℕ) (P : ℚ[X]) :
    IntegrableOn (integrand K P) (Set.Ioi 0) ∧
      aeval zeta5 (μX K P) = ∫ y in Set.Ioi 0, integrand K P y := by sorry

end Apery
