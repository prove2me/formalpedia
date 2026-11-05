-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_NullDirections_frame_null_classification
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.frame_null_classification
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:10.986546+00:00
-- url     : https://prove2.me/theorems/e81437e2-8616-4600-b46b-1dee240b7f07
-- title:
--   Scalar classification
-- statement:
--   **Scalar classification.** With positive frame factors, `0 < u < 1` and `α² > 0`, a nonzero
--   frame vector with `q(v) = 0` and `q(z) = 0` is a nonzero multiple of exactly one of `K_{±√α²}`;
--   conversely these multiples satisfy all three conditions. Both square-root branches are kept.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/MaxwellFrame.lean#L120-L252; SHA-256 ab8c1ad7b3fc2c63531e3072d301ac67c046f773db65e967b4a3e761b9f88908. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Radial
open scoped Matrix

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.NullDirections.frame_null_classification {f D A H u : ℝ} (hf : 0 < f) (hD : 0 < D) (hA : 0 < A)
    (hH : 0 < H) (hu : 0 < u) (hu1 : u < 1) {e a1 : ℝ} (a0 : ℝ)
    (ha2 : 0 < alphaSqFrame f D H e a1) (v : Fin 5 → ℝ) :
    (v ≠ 0 ∧ frameQ f D A H u v = 0 ∧ frameQ f D A H u (frameZ f D A H u e a1 a0 v) = 0) ↔
      ∃ t : ℝ, t ≠ 0 ∧
        (v = t • principalFrame f H e a1 (Real.sqrt (alphaSqFrame f D H e a1)) ∨
          v = t • principalFrame f H e a1 (-Real.sqrt (alphaSqFrame f D H e a1))) := by sorry
