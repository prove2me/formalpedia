-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_VII16R_mvt_bound
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.mvt_bound
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:03:54.806389+00:00
-- url     : https://prove2.me/theorems/1282b4e5-e020-4f1a-a877-b7bc2e00d7cf
-- title:
--   MVT witness
-- statement:
--   MVT witness: a value bound `|g x − c₁x| ≤ Cx²` gives, below each `x`, a point where the
--   derivative is bounded by a constant (no derivative hypothesis beyond differentiability).
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/VII16RFirstOrder.lean#L207-L241; SHA-256 c37ebd91fc832f0ca92cc961a78b3d0265b3e23c4aed113f53001c44db1c66e9. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open Filter Set Topology
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open Filter Set Topology ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.VII16R.mvt_bound {g g' : ℝ → ℝ} {c₁ C δ : ℝ}
    (hd : ∀ x ∈ Ioo (0:ℝ) δ, HasDerivAt g (g' x) x)
    (hb : ∀ x ∈ Ioo (0:ℝ) δ, |g x - c₁ * x| ≤ C * x ^ 2) :
    ∀ x ∈ Ioo (0:ℝ) δ, ∃ ξ ∈ Ioo (0:ℝ) x, |g' ξ| ≤ |c₁| + 3 * |C| * δ := by sorry
