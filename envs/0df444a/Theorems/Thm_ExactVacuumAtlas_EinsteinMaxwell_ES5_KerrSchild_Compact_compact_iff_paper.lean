-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Compact_compact_iff_paper
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact.compact_iff_paper
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:43.234592+00:00
-- url     : https://prove2.me/theorems/a2bcf16a-6105-4eba-96b8-7bf56d44a7db
-- title:
--   At a chart point the four compactified residuals vanish iff the four paper residuals
--   (24a, 24b, 24c left-minus-right, 25) do; the normalising factors are nonzero there
-- statement:
--   At a chart point the four compactified residuals vanish iff the four paper residuals
--   (24a, 24b, 24c left-minus-right, 25) do; the normalising factors are nonzero there.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/CompactifiedBridge.lean#L299-L319; SHA-256 0871e61872db66c0912c0f09d119b86f6b26c1ef4b1385aad9549f01fc411484. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
open scoped ContDiff Topology
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
variable {I : Set ℝ} {s h x : ℝ}
variable {f m N w p a : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact.compact_iff_paper (hP : PaperData I f m N w p a) (hN : FactorizedN I N s h) (hx : x ≠ 0)
    (hxI : s + x⁻¹ ∈ I) (Q J : ℝ) :
    (realPF h Q J (pull s f) (pullM s m) (pull s a) x = 0 ∧
      realPM h Q J (pull s f) (pullM s m) (pull s a) x = 0 ∧
      realPA h Q J (pull s f) (pullM s m) (pull s a) x = 0 ∧
      realPC h Q J (pull s f) (pullM s m) (pull s a) x = 0) ↔
    (paperFResidual f m N a Q (s + x⁻¹) = 0 ∧ paperMResidual f m N a Q J (s + x⁻¹) = 0 ∧
      eq24cResidual f m N a Q J (s + x⁻¹) = 0 ∧
      paperConstraintResidual f m N a Q J (s + x⁻¹) = 0) := by sorry
