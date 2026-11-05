-- Prove2me | Theorems.Thm_ExactVacuumAtlas_EinsteinMaxwell_ES5_KerrSchild_Geodesic_lower_accel
-- name    : ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.lower_accel
-- status  : Proved
-- author  : @He Wang
-- created : 2026-11-04T18:00:20.732556+00:00
-- url     : https://prove2.me/theorems/40533d6f-9181-4750-b892-256432ff1bc5
-- title:
--   Lowered actual acceleration
-- statement:
--   **Lowered actual acceleration.** With `g · ginv = 1` at `x` and genuinely differentiable
--   metric components and field components at `x`:
--   `(g·accel)_b = Σ_j K^j ∂_j (g K)_b - ½ Σ_{j,l} ∂_b(g_{jl}) K^j K^l`. No metric symmetry is used.
--
--   **Scope.** Supporting result in the formal proof chain of Atlas VII Unit A: the restricted geodesic Kerr–Schild obstruction on the actual asymptotic branch of the five-dimensional, $\Lambda = 0$, source-free Einstein–Maxwell radial system with two equal-magnitude angular momenta. It asserts exactly the Lean statement of this node for the data stated there; it does not claim the existence of a solution, a horizon or a black hole.
-- source:
--   He Wang, Exact Spacetime Atlas VII, Unit A (restricted Kerr–Schild obstruction on the actual asymptotic branch, VII17). Local source, no public repository; commit f64ba9c823ec; Atlas/EinsteinMaxwell/ES5/KerrSchild/CoordinateAcceleration.lean#L111-L161; SHA-256 b908ad47b366e1f7c3e1e9f387b2f112cdf3eeb96b6b7a63f3838c7ab394bfc2. Registered definitions: mission/PHYSICS_BOUNDARY.md (Atlas VII sections P–XVII). Physical Kerr–Schild obstruction: Fröb–Khavkine–Málek–Pravda, Eur. Phys. J. C 82 (2022) 215, arXiv:2112.13266 (Eqs. 23–25, 33, 59–60).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_D_Basic
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Defs
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Cert
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Data
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Reduced
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_Generic_Tables
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_CoordinateAcceleration
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_MaxwellFrame
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_PaperGauge
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVP
import Definitions.Def_Atlas_EinsteinMaxwell_ES5_KerrSchild_RadialBVPEquivalence
open scoped ContDiff Topology Matrix
open ExactVacuumAtlas ExactVacuumAtlas.EinsteinMaxwell ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas
open ExactVacuumAtlas.EinsteinMaxwell
open ExactVacuumAtlas.EinsteinMaxwell.ES5
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild
open ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic
variable {n : ℕ}

theorem ExactVacuumAtlas.EinsteinMaxwell.ES5.KerrSchild.Geodesic.lower_accel {g ginv : Metric n} {K : Pt n → Fin n → ℝ} {x : Pt n}
    (hinv : metricMatrix g x * metricMatrix ginv x = 1)
    (hg : ∀ i j, DifferentiableAt ℝ (g i j) x) (hK : ∀ i, DifferentiableAt ℝ (fun y => K y i) x)
    (b : Fin n) :
    (metricMatrix g x *ᵥ accel g ginv K x) b =
      ∑ j, K x j * pd j (fun y => (metricMatrix g y *ᵥ K y) b) x -
        (∑ j, ∑ l, pd b (g j l) x * K x j * K x l) / 2 := by sorry
