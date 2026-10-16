-- Prove2me | Theorems.Thm_ExactVacuumAtlas_christoffel_transform
-- name    : ExactVacuumAtlas.christoffel_transform
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:59:08.933981+00:00
-- url     : https://prove2.me/theorems/55bf3048-2b63-4061-9bf6-a1daa281f0c0
-- title:
--   Transformation of the Christoffel symbols (with the second-derivative term)
-- statement:
--   Under CoordChange U V Φ J K, MetricData h ĥ V and the two pull-back identities on U: for every y ∈ U and every direction index i, connMat (christoffel g ĝ) i y = Σ_e J(y)_{ei} • (K(y) · connMat (christoffel h ĥ) e (Φ y) · J(y)) + K(y) · ∂ᵢJ(y), where (connMat Γ c y)_{ab} = Γ a c b y (first lower index = direction) and ∂ᵢJ = pdM i J is the entrywise slice derivative. Componentwise: Γ[g]ᵏ_{ij}(y) = Σ_c Kᵏ_c (∂ᵢJᶜ_j + Σ_{ab} Γ[h]ᶜ_{ab}(Φ y) Jᵃ_i Jᵇ_j).
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Connection.lean#L330-L365; SHA-256 d9d2c0c550804af1430499fc5d73ee7e2bc88101561ef9f58a7d0037f08372e9. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}
variable {U V : Set (Pt n)} {Φ : Pt n → Pt n} {J K : Pt n → Matrix (Fin n) (Fin n) ℝ}
  {g gi h hi : Metric n}

theorem ExactVacuumAtlas.christoffel_transform (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y)
    (hgi : ∀ y ∈ U, metricMatrix gi y = K y * metricMatrix hi (Φ y) * (K y)ᵀ)
    {y : Pt n} (hy : y ∈ U) (i : Fin n) :
    connMat (christoffel g gi) i y
      = ∑ e, J y e i • (K y * connMat (christoffel h hi) e (Φ y) * J y) + K y * pdM i J y := by sorry
