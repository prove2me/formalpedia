-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Radial_PaperData_toESData
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial.PaperData.toESData
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:17.051003+00:00
-- url     : https://prove2.me/theorems/4c58647d-64c4-4893-ae5e-a48c47010218
-- title:
--   The dictionary yields the VI radial data; only regularity and non-vanishing are used
-- statement:
--   The dictionary yields the VI radial data; only regularity and non-vanishing are used.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/PaperGauge.lean#L86-L100; SHA-256 98230967976fc2d4ca8c7d7330dc9d38fa71be76c28db9b6c447ed12bd308d26. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
open scoped ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ} {r : ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial.PaperData.toESData (hP : PaperData I f m N w p a) :
    ESData I f (Dfun f m N) (Afun f m) (Hfun m N) w p a := by sorry
