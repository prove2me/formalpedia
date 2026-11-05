-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geodesic_vii07_ricci_null_pregeodesic_G_zero
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.vii07_ricci_null_pregeodesic_G_zero
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:01:57.19707+00:00
-- url     : https://prove2.me/theorems/1955b23b-196f-4a0c-9311-27888d57ea14
-- title:
--   Root (arbitrary actual Ricci-null pregeodesic field ⇒ G = 0)
-- statement:
--   **Root (arbitrary actual Ricci-null pregeodesic field ⇒ `G = 0`).** `U` open, `U ⊆ esDomain I`,
--   `f, m, N, alphaSq > 0` and the candidate's own actual Einstein–Maxwell equations on `U`; `V` is
--   `C¹` on `U` and at every point of `U` nonzero, actually null, actually Ricci-null and actually
--   pregeodesic. Then `G(x 1) = 0` for all `x ∈ U`. No principal alignment, sign choice, stationarity
--   or `G = 0` premise; no connectedness of `U`; the multiplier is not assumed continuous.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/GeodesicCongruenceObstruction.lean#L217-L246; SHA-256 40c3447b42aa46d0a5a728dada1ccd4d602bdb3f202b0c97df6a35ba79c094e7. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_OneSidedExtraction
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
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Compact
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.SmoothExt
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
open ExactVacuumAtlas.EinsteinMaxwell.D (einsteinMaxwellD EMCertificateD)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.vii07_ricci_null_pregeodesic_G_zero (hP : PaperData I f m N w p a) {U : Set (Pt 5)}
    (hU : IsOpen U) (hUI : U ⊆ esDomain I)
    (hpos : ∀ x ∈ U, 0 < f (x 1) ∧ 0 < m (x 1) ∧ 0 < N (x 1) ∧ 0 < alphaSq f m N w p a (x 1))
    (hEin : ∀ x ∈ U, ∀ i j, einsteinMaxwellD (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
      (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) (esFaraday p a) i j x = 0)
    {V : Pt 5 → Fin 5 → ℝ} (hV : ∀ i, ContDiffOn ℝ 1 (fun x => V x i) U)
    (hNZ : ∀ x ∈ U, V x ≠ 0)
    (hnull : ∀ x ∈ U, contract2 (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w) x (V x) = 0)
    (hRic : ∀ x ∈ U, contract2 (ricciOf (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
      (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w)) x (V x) = 0)
    (hgeo : ∀ x ∈ U, PregeodesicAt (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
      (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) V x) :
    ∀ x ∈ U, Gfun p a (x 1) = 0 := by sorry
