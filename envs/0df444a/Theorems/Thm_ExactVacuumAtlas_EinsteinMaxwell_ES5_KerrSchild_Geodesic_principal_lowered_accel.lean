-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geodesic_principal_lowered_accel
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.principal_lowered_accel
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:03:11.254089+00:00
-- url     : https://prove2.me/theorems/6bec5420-1d57-4825-83ff-70ff1a62e21a
-- title:
--   Lowered actual acceleration
-- statement:
--   **Lowered actual acceleration** of `principalField λ` at `x ∈ esDomain I`, for any radial `λ`
--   with a genuine derivative at `R = x 1` and `λ² = alphaSq` on a neighbourhood of `R`:
--   `g·accel = (-λp'', (e/f)(p'' + w a'') - a'a''/H, 0, -uλa'', -(1-u)λa'')`.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/PrincipalGeodesic.lean#L120-L218; SHA-256 5452b99cefb6ce9580bc3a7cd3b092cf372b1834cc7796fc323f927c83b7b637. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ChargedTail
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedBridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedResiduals
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CoordinateAcceleration
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PrincipalGeodesic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RicciNullDirections
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
open scoped ContDiff Topology Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.principal_lowered_accel (hP : PaperData I f m N w p a) {x : Pt 5} (hx : x ∈ esDomain I)
    {lam : ℝ → ℝ} {lam' : ℝ} (hlam : HasDerivAt lam lam' (x 1))
    (hsq : ∀ᶠ r in 𝓝 (x 1), lam r ^ 2 = alphaSq f m N w p a r) :
    metricMatrix (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w) x *ᵥ
        accel (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
          (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) (principalField f m N w p a lam) x =
      ![-(lam (x 1) * deriv (deriv p) (x 1)),
        eFun w p a (x 1) / f (x 1) * (deriv (deriv p) (x 1) + w (x 1) * deriv (deriv a) (x 1)) -
          deriv a (x 1) * deriv (deriv a) (x 1) / Hfun m N (x 1),
        0, -(x 2 * lam (x 1) * deriv (deriv a) (x 1)),
        -((1 - x 2) * lam (x 1) * deriv (deriv a) (x 1))] := by sorry
