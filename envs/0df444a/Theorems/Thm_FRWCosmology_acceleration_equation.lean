-- Prove2me | Theorems.Thm_FRWCosmology_acceleration_equation
-- name    : FRWCosmology.acceleration_equation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T00:45:48.500129+00:00
-- url     : https://prove2.me/theorems/900dc249-6fea-41af-af54-09bd25a20b4e
-- title:
--   Acceleration equation $\ddot a/a = -\frac{4\pi G}{3}(\rho + 3p)$
-- statement:
--   In any FRW universe, at every time $t$ of the domain,
--
--   $$\frac{\ddot a(t)}{a(t)} \;=\; -\frac{4\pi G}{3}\bigl(\rho(t) + 3p(t)\bigr).$$
--
--   This is the acceleration equation: it is obtained by eliminating the curvature term between
--   the two Friedmann equations, and it shows that the sign of $\ddot a$ is the sign of
--   $-(\rho + 3p)$, since the scale factor is positive.
-- source:
--   Konstantinos Xenos, An Introduction to FRW Cosmology and dark energy models, University of Patras undergraduate thesis, 2020, arXiv:2101.06135v1, https://arxiv.org/abs/2101.06135, p. 57, eq. (4.27)

import Definitions.Def_FRWUniverse

namespace FRWCosmology

theorem acceleration_equation (U : FRWUniverse) (t : ℝ) (ht : t ∈ U.I) :
    U.addot t / U.a t = -(4 * Real.pi * U.G / 3) * (U.rho t + 3 * U.p t) := by sorry

end FRWCosmology
