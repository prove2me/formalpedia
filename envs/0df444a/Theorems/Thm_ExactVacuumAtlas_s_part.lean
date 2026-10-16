-- Prove2me | Theorems.Thm_ExactVacuumAtlas_s_part
-- name    : ExactVacuumAtlas.s_part
-- status  : Proved
-- author  : @He Wang
-- created : 2026-10-15T20:52:52.458193+00:00
-- url     : https://prove2.me/theorems/361840f7-6198-428c-8b10-94f1dc5764a6
-- title:
--   Algebraic core: second-derivative part of the Christoffel transformation
-- statement:
--   Pure matrix identity: for symmetric H and matrices Si, Sj, Sl with the stated symmetries (Sj a l = Sl a j, Si a l = Sl a i, Sj a i = Si a j), the six S-terms (Sjᵀ H Jm)_{li} + (Jmᵀ H Sj)_{li} + (Siᵀ H Jm)_{lj} + (Jmᵀ H Si)_{lj} − (Slᵀ H Jm)_{ij} − (Jmᵀ H Sl)_{ij} collapse to 2 Σ_a Jm_{al} Σ_b H_{ab} Si_{bj}.
-- source:
--   He Wang, Exact Vacuum Atlas II, local source snapshot (public Git repository not yet available), commit 11fb317259353b71a41d6daed466c495cffd7db4; Atlas/Transport/Connection.lean#L185-L202; SHA-256 d9d2c0c550804af1430499fc5d73ee7e2bc88101561ef9f58a7d0037f08372e9. Mathematical background: See mission/PHYSICS_BOUNDARY.md §A-F for registered definitions and literature references (Wald, Müller-Grave arXiv:0904.4184, Visser arXiv:0706.0622, Martel-Poisson gr-qc/0001069).

import Mathlib
import Definitions.Def_Atlas_Core_Basic
import Definitions.Def_Atlas_Core_Certificate
import Definitions.Def_Atlas_Transport_Connection
import Definitions.Def_Atlas_Transport_MatrixCalc
open scoped ContDiff
open Matrix
open ExactVacuumAtlas
variable {n : ℕ}

theorem ExactVacuumAtlas.s_part {Jm H Si Sj Sl : Matrix (Fin n) (Fin n) ℝ} (hH : H.transpose = H) {i j l : Fin n}
    (hjl : ∀ a, Sj a l = Sl a j) (hil : ∀ a, Si a l = Sl a i) (hji : ∀ a, Sj a i = Si a j) :
    (Sj.transpose * H * Jm) l i + (Jm.transpose * H * Sj) l i
      + (Si.transpose * H * Jm) l j + (Jm.transpose * H * Si) l j
      - (Sl.transpose * H * Jm) i j - (Jm.transpose * H * Sl) i j
      = 2 * ∑ a, Jm a l * ∑ b, H a b * Si b j := by sorry
