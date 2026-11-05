-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_NullDirections_vii06_ricci_null_directions
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.vii06_ricci_null_directions
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:12.126522+00:00
-- url     : https://prove2.me/theorems/4cb9cfec-58e0-4cb0-8d97-319e4b0f40fe
-- title:
--   Root B (actual pointwise Ricci-null classification)
-- statement:
--   **Root B (actual pointwise Ricci-null classification).** At a point of the actual domain with
--   `f, m, N > 0` and `alphaSq > 0`, where the candidate's own Einstein–Maxwell equations hold:
--   the actual principal vectors `k₊, k₋` are eigenvectors of the actual `g⁻¹ F` with eigenvalues
--   `±√alphaSq` and are not proportional; and a coordinate vector `k` is nonzero, actually null and
--   actually Ricci-null iff it is a nonzero multiple of `k₊` or of `k₋`.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/RicciNullDirections.lean#L198-L288; SHA-256 fb339251f052ff4695654aac2e883ce515ebfe42debf1c34d3031326fbfd3f29. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.vii06_ricci_null_directions (hP : PaperData I f m N w p a) {x : Pt 5}
    (hx : x ∈ esDomain I) (hf : 0 < f (x 1)) (hm : 0 < m (x 1)) (hN : 0 < N (x 1))
    (ha2 : 0 < alphaSq f m N w p a (x 1))
    (hEin : ∀ i j, einsteinMaxwellD (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
      (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) (esFaraday p a) i j x = 0) :
    (metricMatrix (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) x *
        metricMatrix (esFaraday p a) x) *ᵥ kPlus f m N w p a x =
        Real.sqrt (alphaSq f m N w p a (x 1)) • kPlus f m N w p a x ∧
      (metricMatrix (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) x *
        metricMatrix (esFaraday p a) x) *ᵥ kMinus f m N w p a x =
        (-Real.sqrt (alphaSq f m N w p a (x 1))) • kMinus f m N w p a x ∧
      (∀ c : ℝ, kPlus f m N w p a x ≠ c • kMinus f m N w p a x ∧
        kMinus f m N w p a x ≠ c • kPlus f m N w p a x) ∧
      ∀ k : Fin 5 → ℝ,
        (k ≠ 0 ∧ contract2 (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w) x k = 0 ∧
          contract2 (ricciOf (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
            (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w)) x k = 0) ↔
        ∃ t : ℝ, t ≠ 0 ∧ (k = t • kPlus f m N w p a x ∨ k = t • kMinus f m N w p a x) := by sorry
