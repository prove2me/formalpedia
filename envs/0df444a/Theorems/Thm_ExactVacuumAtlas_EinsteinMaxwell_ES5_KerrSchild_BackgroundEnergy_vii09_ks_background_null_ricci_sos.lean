-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_BackgroundEnergy_vii09_ks_background_null_ricci_sos
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.BackgroundEnergy.vii09_ks_background_null_ricci_sos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:32.521801+00:00
-- url     : https://prove2.me/theorems/817a81a1-3734-46cb-b35b-3d5dc69f2d1e
-- title:
--   Root (background inherits the actual SOS)
-- statement:
--   **Root (background inherits the actual SOS).** At a point of `U ⊆ esDomain I` where `K` is
--   actually background-pregeodesic, `f, m, N > 0`, `alphaSq > 0` and the actual `PaperBVP` holds:
--   `Ric_gb(K,K) = Ric_gA(K,K) = c₀L² + c₂ξ₂² + c₄ξ₄² ≥ mu·misalign ≥ 0`, `mu > 0`.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/KSBackgroundEnergy.lean#L136-L157; SHA-256 d817b93e8e7388c86e08169a286a395342d39320ec1edd99fbb7c5efe7c434e4. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteJetObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_FiniteTaylorJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_GeodesicCongruenceObstruction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_JetRecursion
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSBackgroundEnergy
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSConnection
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSMetric
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_KSRicci
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_NullRicciEnergy
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_OneSidedExtraction
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PrincipalGeodesic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RicciNullDirections
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
import Definitions.Def_Atlas_Transport_Connection
open scoped ContDiff Topology Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.SmoothExt
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geometry
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullEnergy
open ExactVacuumAtlas.EinsteinMaxwell.D (einsteinMaxwellD EMCertificateD)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.BackgroundEnergy
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ} {gb gbi : Metric 5} {v : Pt 5 → ℝ}
  {K : Pt 5 → Fin 5 → ℝ} {U : Set (Pt 5)}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.BackgroundEnergy.vii09_ks_background_null_ricci_sos {Q J : ℝ} (hP : PaperData I f m N w p a)
    (hB : PaperBVP I f m N w p a Q J) (hUI : U ⊆ esDomain I) (hD : KSData gb gbi v K U)
    (hrep : ∀ i j, Set.EqOn (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w i j)
      (ksMetric gb v K i j) U) {x : Pt 5} (hx : x ∈ U) (hg : PregeodesicAt gb gbi K x)
    (hf : 0 < f (x 1)) (hm : 0 < m (x 1)) (hN : 0 < N (x 1))
    (ha2 : 0 < alphaSq f m N w p a (x 1)) :
    contract2 (ricciOf gb gbi) x (K x) =
        contract2 (ricciOf (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
          (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w)) x (K x) ∧
      contract2 (ricciOf gb gbi) x (K x) = nullSOS f m N w p a x (K x) ∧
      muCoeff f m N w p a x * misalign f m N w p a x (K x) ≤
        contract2 (ricciOf gb gbi) x (K x) ∧
      0 ≤ muCoeff f m N w p a x * misalign f m N w p a x (K x) ∧
      0 < muCoeff f m N w p a x := by sorry
