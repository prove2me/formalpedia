-- Prove2me | Theorems.Thm_ExactVacuumAtlas_d_part
-- name    : ExactVacuumAtlas.d_part
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:49:00.431835+00:00
-- url     : https://prove2.me/theorems/dc89ff69-ba35-4f28-a97d-a2158d92bbf9
-- title:
--   Algebraic core: first-derivative part of the Christoffel transformation
-- statement:
--   Pure matrix identity (no calculus): for a matrix Jm and a 3-index array D with Di, Dj, Dl the contractions D·Jm in the third index with columns i, j, l: (Jmᵀ Dj Jm)_{li} + (Jmᵀ Di Jm)_{lj} − (Jmᵀ Dl Jm)_{ij} = 2 Σ_a Jm_{al} Σ_{b,e} Jm_{bi} Jm_{ej} (D_{abe} + D_{aeb} − D_{bea})/2.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Connection.lean#L204-L247; SHA-256 d9d2c0c550804af1430499fc5d73ee7e2bc88101561ef9f58a7d0037f08372e9. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.d_part {Jm : Matrix (Fin n) (Fin n) ℝ} {D : Fin n → Fin n → Fin n → ℝ} {i j l : Fin n}
    (Di Dj Dl : Matrix (Fin n) (Fin n) ℝ)
    (hDi : ∀ a b, Di a b = ∑ e, D a b e * Jm e i) (hDj : ∀ a b, Dj a b = ∑ e, D a b e * Jm e j)
    (hDl : ∀ a b, Dl a b = ∑ e, D a b e * Jm e l) :
    (Jm.transpose * Dj * Jm) l i + (Jm.transpose * Di * Jm) l j - (Jm.transpose * Dl * Jm) i j
      = 2 * ∑ a, Jm a l * ∑ b, ∑ e, Jm b i * Jm e j * ((D a b e + D a e b - D b e a) / 2) := by sorry
