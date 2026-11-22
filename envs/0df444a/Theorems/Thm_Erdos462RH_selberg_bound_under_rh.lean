-- Prove2me | Theorems.Thm_Erdos462RH_selberg_bound_under_rh
-- name    : Erdos462RH.selberg_bound_under_rh
-- status  : Open
-- author  : @adamhenr
-- created : 2026-11-21T09:06:31.977877+00:00
-- url     : https://prove2.me/theorems/d009141d-91b5-4573-ba1d-e1b8dbeffd79
-- title:
--   The relative theta Selberg estimate under classical RH
-- statement:
--   Assume the Riemann hypothesis for the Riemann zeta function. For all real $Y\ge 10^{13}$ and $0<d\le10^{-13}$,
--   $$J_\theta(Y,d)\le 2.5571\,dY^2\log^2(2.0001/d).$$
--   This is the published analytic input in the semiprime theorem.
-- source:
--   A. Chirre and M. V. Hagen, On Goldbach numbers in short intervals, Theorem 3, https://doi.org/10.1007/s40993-026-00767-6. Adam Henriksson, Balanced semiprimes in short intervals under the Riemann hypothesis. Section 2, equation (1).

import Definitions.Def_Erdos462Selberg

namespace Erdos462RH
theorem selberg_bound_under_rh (h : RiemannHypothesis) : SelbergBound := by sorry
end Erdos462RH
