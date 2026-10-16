-- Prove2me | Theorems.Thm_ExactVacuumAtlas_ricciOf_transform
-- name    : ExactVacuumAtlas.ricciOf_transform
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:05:38.892212+00:00
-- url     : https://prove2.me/theorems/9ba65ba2-f857-4310-b2c8-5b0c3d9f148e
-- title:
--   Transformation law of ricciOf (the theorem behind the Goal)
-- statement:
--   Exactly the statement of Release02.ricci_law (same hypotheses CoordChange, MetricData, two pull-back identities; same conclusion with the two Jacobian factors), stated with y implicit; ricci_law is its one-line wrapper.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Ricci.lean#L65-L109; SHA-256 342fc31f65dc80056511ed63312ec5952dbdd161e5928b65599507f297dcfc60. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

theorem ExactVacuumAtlas.ricciOf_transform (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ)
    {y : Pt n} (hy : y ∈ U) (i j : Fin n) :
    ricciOf g gi i j y = ∑ a, ∑ b, J y a i * J y b j * ricciOf h hi a b (Φ y) := by sorry
