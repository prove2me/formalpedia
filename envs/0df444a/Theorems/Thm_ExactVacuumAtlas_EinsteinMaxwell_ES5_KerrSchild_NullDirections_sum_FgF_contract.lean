-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_NullDirections_sum_FgF_contract
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.sum_FgF_contract
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:19.018314+00:00
-- url     : https://prove2.me/theorems/4c14aebd-50de-4b46-8a95-eea7fe6e2ffb
-- title:
--   Σ_ab (Σ_cd F_ac gⁱ_cd F_bd) k^a k^b = Σ_cd gⁱ_cd y_c y_d, y_c = Σ_a F_ac k^a
-- statement:
--   `Σ_ab (Σ_cd F_ac gⁱ_cd F_bd) k^a k^b = Σ_cd gⁱ_cd y_c y_d`, `y_c = Σ_a F_ac k^a`.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/RicciNullDirections.lean#L38-L58; SHA-256 fb339251f052ff4695654aac2e883ce515ebfe42debf1c34d3031326fbfd3f29. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.sum_FgF_contract {n : ℕ} (F gi : Fin n → Fin n → ℝ) (k : Fin n → ℝ) :
    ∑ a, ∑ b, (∑ c, ∑ d, F a c * gi c d * F b d) * k a * k b =
      ∑ c, ∑ d, (∑ a, F a c * k a) * gi c d * (∑ b, F b d * k b) := by sorry
