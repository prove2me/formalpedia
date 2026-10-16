-- Prove2me | Theorems.Thm_ExactVacuumAtlas_inv_mul_pullC
-- name    : ExactVacuumAtlas.inv_mul_pullC
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:57:20.395919+00:00
-- url     : https://prove2.me/theorems/4af93564-5fdb-4416-b72a-c498e175c018
-- title:
--   ĥ · Cᵢ = (Σ_b J_{bi} Γ̄_b) · J
-- statement:
--   For any metrics h, ĥ, map Φ, Jacobian field J, point y and index i: ĥ(Φ y) · pullC h Φ J y i = (Σ_b J y b i • connMat (christoffel h ĥ) b (Φ y)) · J y. Pure algebra from the definitions of pullC, chr1 and christoffel.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Connection.lean#L313-L328; SHA-256 d9d2c0c550804af1430499fc5d73ee7e2bc88101561ef9f58a7d0037f08372e9. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

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

theorem ExactVacuumAtlas.inv_mul_pullC (h hi : Metric n) (Φ : Pt n → Pt n) (J : Pt n → Matrix (Fin n) (Fin n) ℝ)
    (y : Pt n) (i : Fin n) :
    metricMatrix hi (Φ y) * pullC h Φ J y i
      = (∑ b, J y b i • connMat (christoffel h hi) b (Φ y)) * J y := by sorry
