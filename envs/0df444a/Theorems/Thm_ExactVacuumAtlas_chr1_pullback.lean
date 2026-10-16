-- Prove2me | Theorems.Thm_ExactVacuumAtlas_chr1_pullback
-- name    : ExactVacuumAtlas.chr1_pullback
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:54:39.166065+00:00
-- url     : https://prove2.me/theorems/57a37664-527d-4b3c-9157-8040be7591f8
-- title:
--   First-kind Christoffel symbols of the pulled-back metric
-- statement:
--   Under CoordChange U V Φ J K, MetricData h ĥ V and g = Jᵀ h(Φ) J on U: for y ∈ U and all l, i, j, chr1 g l i j y = ((J y)ᵀ · (h(Φ y) · ∂ᵢJ(y) + pullC h Φ J y i))_{lj}, with chr1 g l i j = ½(∂_j g_{li} + ∂_i g_{lj} − ∂_l g_{ij}) and pullC the pulled-back first-kind symbols of h.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Connection.lean#L285-L311; SHA-256 d9d2c0c550804af1430499fc5d73ee7e2bc88101561ef9f58a7d0037f08372e9. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.chr1_pullback (hc : CoordChange U V Φ J K) (hm : MetricData h hi V)
    (hg : ∀ y ∈ U, metricMatrix g y = (J y)ᵀ * metricMatrix h (Φ y) * J y) {y : Pt n}
    (hy : y ∈ U) (l i j : Fin n) :
    chr1 g l i j y = ((J y)ᵀ * (metricMatrix h (Φ y) * pdM i J y + pullC h Φ J y i)) l j := by sorry
