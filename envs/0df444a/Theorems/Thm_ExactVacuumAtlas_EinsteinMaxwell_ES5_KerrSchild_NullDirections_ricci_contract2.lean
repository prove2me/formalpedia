-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_NullDirections_ricci_contract2
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.ricci_contract2
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:28.451507+00:00
-- url     : https://prove2.me/theorems/adc877cd-7996-48aa-a27d-3fff40d285e9
-- title:
--   Contracted actual field equations
-- statement:
--   **Contracted actual field equations.** If the candidate's own Einstein–Maxwell equations hold
--   at `x`, then `Ric(k,k) = 2 q(z) - g(k,k) F²/3` for every actual coordinate vector `k`, where `q(z)`
--   is the frame form of the actual mixed vector.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/RicciNullDirections.lean#L94-L119; SHA-256 fb339251f052ff4695654aac2e883ce515ebfe42debf1c34d3031326fbfd3f29. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RicciNullDirections
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.SmoothExt
open ExactVacuumAtlas.EinsteinMaxwell.D (einsteinMaxwellD EMCertificateD)
open scoped Matrix
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
variable {R : Set ℝ} {B D A H W Φ Ψ : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.ricci_contract2 (hE : ESData R B D A H W Φ Ψ) {x : Pt 5} (hx : x ∈ esDomain R)
    (hEin : ∀ i j, einsteinMaxwellD (esMetric B D A H W) (esInverse B D A H W)
      (esFaraday Φ Ψ) i j x = 0) (k : Fin 5 → ℝ) :
    contract2 (ricciOf (esMetric B D A H W) (esInverse B D A H W)) x k =
      2 * frameQ (B (x 1)) (D (x 1)) (A (x 1)) (H (x 1)) (x 2)
        (frameZ (B (x 1)) (D (x 1)) (A (x 1)) (H (x 1)) (x 2)
          (deriv Φ (x 1) + W (x 1) * deriv Ψ (x 1)) (deriv Ψ (x 1)) (Ψ (x 1)) (frameInv W x k)) -
      contract2 (esMetric B D A H W) x k * fieldSq (esInverse B D A H W) (esFaraday Φ Ψ) x / 3 := by sorry
