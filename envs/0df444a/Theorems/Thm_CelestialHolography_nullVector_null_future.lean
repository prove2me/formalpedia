-- Prove2me | Theorems.Thm_CelestialHolography_nullVector_null_future
-- name    : CelestialHolography.nullVector_null_future
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T01:42:39.077992+00:00
-- url     : https://prove2.me/theorems/41c8915e-adc8-4af8-af0f-c332071c9466
-- title:
--   Eq. (11): $q^\mu(z,\bar z)$ is a future-directed null vector
-- statement:
--   For every $z\in\mathbb C$, the vector $q(z)=\tfrac1{\sqrt2}(1+|z|^2,\,z+\bar z,\,-i(z-\bar z),\,1-|z|^2)$ of eq. (11) satisfies
--   $$\|q(z)\|_\eta^2=0\qquad\text{and}\qquad q^0(z)>0,$$
--   i.e. $q(z)$ is null and future-directed, so $p^\mu=\omega q^\mu(z)$ with $\omega>0$ is the momentum of a massless particle of energy proportional to $\omega$.
-- source:
--   F. Barzi, *Celestial Holography, A Hitchhiker's Guide to the Celestial Sphere*, arXiv:2608.07568v1 [hep-th], https://arxiv.org/abs/2608.07568

import Mathlib
import Definitions.Def_CelestialHolography_LorentzMobius_Defs

namespace CelestialHolography

theorem nullVector_null_future (z : ℂ) :
    minkowskiNormSq (nullVector z) = 0 ∧ 0 < nullVector z 0 := by sorry

end CelestialHolography
