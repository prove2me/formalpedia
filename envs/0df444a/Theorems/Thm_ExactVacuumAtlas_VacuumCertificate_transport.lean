-- Prove2me | Theorems.Thm_ExactVacuumAtlas_VacuumCertificate_transport
-- name    : ExactVacuumAtlas.VacuumCertificate.transport
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T21:24:37.222786+00:00
-- url     : https://prove2.me/theorems/77e42834-3aca-43c4-aa29-39ac8e39326c
-- title:
--   Certificate transport along a CoordChange (total dimension m + 1)
-- statement:
--   Total dimension m + 1 (any m). Under CoordChange U V Φ J K, U nonempty, a vacuum certificate for (h, ĥ) on V, and the two pull-back identities g = Jᵀ h(Φ) J and ĝ = K ĥ(Φ) Kᵀ on U: (g, ĝ) carries a vacuum certificate on U (all eight obligations; Lorentz frame K·E; Ricci by ricciOf_transform).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Certificate.lean#L44-L62; SHA-256 ba79c925752e43cb527671a3db9842422fb083444c4304ff7763fdb1c1f68683. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Core_Relation
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_Curvature
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {m : ℕ} {U V : Set (Pt (m + 1))} {Φ : Pt (m + 1) → Pt (m + 1)}
  {J K : Pt (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ} {g gi h hi : Metric (m + 1)}

theorem ExactVacuumAtlas.VacuumCertificate.transport (hc : CoordChange U V Φ J K) (hne : U.Nonempty)
    (hcert : VacuumCertificate h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ) :
    VacuumCertificate g gi U := by sorry
