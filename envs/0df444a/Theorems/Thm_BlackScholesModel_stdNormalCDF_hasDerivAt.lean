-- Prove2me | Theorems.Thm_BlackScholesModel_stdNormalCDF_hasDerivAt
-- name    : BlackScholesModel.stdNormalCDF_hasDerivAt
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:28:14.304256+00:00
-- url     : https://prove2.me/theorems/f6dd16e4-91e7-4f24-a809-27da84e200ab
-- title:
--   $N' = dN/dx$: the normal density is the derivative of the normal distribution function
-- statement:
--   Let $N(x)=\frac1{\sqrt{2\pi}}\int_{-\infty}^x e^{-z^2/2}\,dz$ be the standard normal distribution function and $N'(x)=\frac1{\sqrt{2\pi}}e^{-x^2/2}$ the standard normal density. Then for every real $x$, $N$ is differentiable at $x$ and
--
--   $$\frac{dN}{dx}(x)=\frac1{\sqrt{2\pi}}e^{-x^2/2}.$$
--
--   This justifies the notation $N'$ used throughout the Black–Scholes formulas, in particular in the Greeks.
-- source:
--   Wikipedia, "Black–Scholes model" (snapshot supplied as Black–Scholes_model.pdf, 22 pp.), https://en.wikipedia.org/wiki/Black%E2%80%93Scholes_model; p. 3 (Notation: N(x) and N'(x) = dN(x)/dx)

import Mathlib
import Definitions.Def_BlackScholesModel_Core

open Real MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace BlackScholesModel

theorem stdNormalCDF_hasDerivAt (x : ℝ) :
    HasDerivAt stdNormalCDF (stdNormalPDF x) x := by sorry

end BlackScholesModel
