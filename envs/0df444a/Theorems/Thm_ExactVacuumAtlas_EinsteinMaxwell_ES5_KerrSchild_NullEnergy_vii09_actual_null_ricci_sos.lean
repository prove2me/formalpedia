-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_NullEnergy_vii09_actual_null_ricci_sos
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullEnergy.vii09_actual_null_ricci_sos
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T17:59:33.894528+00:00
-- url     : https://prove2.me/theorems/b76353ff-c6ee-4659-88ab-f919993864c1
-- title:
--   Root (actual null Ricci sum of squares)
-- statement:
--   **Root (actual null Ricci sum of squares).** At an actual domain point with `f, m, N > 0`,
--   `alphaSq > 0` and the actual Einstein–Maxwell equations, every actually null `k` satisfies
--   `Ric(k,k) = c₀L² + c₂ξ₂² + c₄ξ₄²` with `c₀ = 8`; `mu > 0`; `Ric(k,k) ≥ mu·misalign ≥ 0`; and
--   `Ric(k,k) = 0` iff the three residuals vanish iff `misalign = 0`. The bound is pointwise in the
--   fixed chart and numerical units; `misalign` is not an invariant or a physical observable.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/NullRicciEnergy.lean#L208-L248; SHA-256 70e4af6f35074a925369db1c80c437687dda58ca8dd01131091fded7e18d928f. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

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
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_NullRicciEnergy
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PolynomialJet
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RicciNullDirections
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_ScalarCertificate
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_SmoothBranch
open scoped Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections
open ExactVacuumAtlas.EinsteinMaxwell.D (einsteinMaxwellD)
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullEnergy
variable {I : Set ℝ} {f m N w p a : ℝ → ℝ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullEnergy.vii09_actual_null_ricci_sos (hP : PaperData I f m N w p a) {x : Pt 5}
    (hx : x ∈ esDomain I) (hf : 0 < f (x 1)) (hm : 0 < m (x 1)) (hN : 0 < N (x 1))
    (ha2 : 0 < alphaSq f m N w p a (x 1))
    (hEin : ∀ i j, einsteinMaxwellD (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
      (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w) (esFaraday p a) i j x = 0)
    {k : Fin 5 → ℝ} (hnull : contract2 (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w) x k = 0) :
    contract2 (ricciOf (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
        (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w)) x k = nullSOS f m N w p a x k ∧
      coeff0 f m N (x 1) = 8 ∧ 0 < muCoeff f m N w p a x ∧
      muCoeff f m N w p a x * misalign f m N w p a x k ≤
        contract2 (ricciOf (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
          (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w)) x k ∧
      0 ≤ muCoeff f m N w p a x * misalign f m N w p a x k ∧
      (contract2 (ricciOf (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
          (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w)) x k = 0 ↔
        resL f m N w p a x k = 0 ∧ frameInv w x k 2 = 0 ∧ frameInv w x k 4 = 0) ∧
      (contract2 (ricciOf (esMetric f (Dfun f m N) (Afun f m) (Hfun m N) w)
          (esInverse f (Dfun f m N) (Afun f m) (Hfun m N) w)) x k = 0 ↔
        misalign f m N w p a x k = 0) := by sorry
