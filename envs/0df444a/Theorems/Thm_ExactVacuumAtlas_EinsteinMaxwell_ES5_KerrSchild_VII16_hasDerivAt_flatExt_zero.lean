-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VII16_hasDerivAt_flatExt_zero
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16.hasDerivAt_flatExt_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:03:48.37998+00:00
-- url     : https://prove2.me/theorems/a0841af7-070a-43b5-a7f0-137aae372dea
-- title:
--   Derivative at the origin of the flat (zero) extension
-- statement:
--   Let $h$ be differentiable on $(0, \varepsilon)$ with $h(x) \to 0$ and $h'(x) \to 0$ as $x \to 0^+$. Then the extension of $h$ by zero to $x \le 0$ (`flatExt h`) has derivative $0$ at the origin.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/VII16AsymptoticBridge.lean#L149-L196; SHA-256 4eaa449e244a96eb98e0a117308c07eff0f4f640fba2fcee9d527fee281fb022. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedBridge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CompactifiedResiduals
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteJetObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylorJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_JetRecursion
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_OneSidedExtraction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII13FiniteBranchSpec
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_VII16AsymptoticBridge
open Filter Set
open scoped Topology ContDiff
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact (pull pullM)
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII13FiniteBranchSpec (FiniteBranch6)
-- (open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.SmoothExt.Controls: no listed name exists here)
-- (open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial: no listed name exists here)

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16.hasDerivAt_flatExt_zero {h : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hdiff : DifferentiableOn ℝ h (Ioo (0:ℝ) ε))
    (hlim0 : Tendsto h (𝓝[>] (0:ℝ)) (𝓝 0))
    (hlim1 : Tendsto (deriv h) (𝓝[>] (0:ℝ)) (𝓝 0)) :
    HasDerivAt (flatExt h) 0 0 := by sorry
