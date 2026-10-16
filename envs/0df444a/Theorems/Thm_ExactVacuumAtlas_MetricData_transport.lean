-- Prove2me | Theorems.Thm_ExactVacuumAtlas_MetricData_transport
-- name    : ExactVacuumAtlas.MetricData.transport
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:46:59.294386+00:00
-- url     : https://prove2.me/theorems/c65b73cf-98b6-4d19-ab93-022b9f1eb6b1
-- title:
--   Metric data transport
-- statement:
--   Under CoordChange U V Φ J K, MetricData h ĥ V and the two pull-back identities g = Jᵀ h(Φ) J, ĝ = K ĥ(Φ) Kᵀ on U: MetricData g ĝ U — the pulled-back metric is symmetric, ĝ · g = I on U, and both are C^∞ on U.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Ricci.lean#L37-L63; SHA-256 342fc31f65dc80056511ed63312ec5952dbdd161e5928b65599507f297dcfc60. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.MetricData.transport (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ) :
    MetricData g gi U := by sorry
