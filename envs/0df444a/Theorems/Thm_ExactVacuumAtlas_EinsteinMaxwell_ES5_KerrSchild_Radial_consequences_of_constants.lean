-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Radial_consequences_of_constants
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial.consequences_of_constants
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:03:24.237806+00:00
-- url     : https://prove2.me/theorems/54a916c0-9ce1-4919-b799-a68669ba356c
-- title:
--   Pointwise consequences of q = -Q, ℓ = -2J and redJ_σ = 0
-- statement:
--   Pointwise consequences of `q = -Q`, `ℓ = -2J` and `redJ_σ = 0`: `e`, `w'` and Eq. 24c.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/RadialConservation.lean#L111-L143; SHA-256 536196d41b98b82a1492ff5efeec9f17458c8e8cdda0ac87064f18d55ece08de. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
open scoped ContDiff
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.D
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ} {r : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial.consequences_of_constants (hP : PaperData I f m N w p a) (hr : r ∈ I) {Q J : ℝ}
    (hq : qFun f N w p a r = -Q) (hl : ellFun f m N w p a r = -2 * J)
    (hJs : Generic.redJ_σ f (Dfun f m N) (Afun f m) (Hfun m N) w p a r = 0) :
    eFun w p a r = -Q * f r / N r ∧
      deriv w r = -2 * (J + 2 * Q * a r) * f r * m r / N r ^ 2 ∧
      m r * deriv (fun s => m s * deriv a s) r - f r * a r =
        2 * Q * f r * m r ^ 2 / N r ^ 2 * (J + 2 * Q * a r) := by sorry
