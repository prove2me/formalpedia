-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_affMat_close
-- name    : BookProof.QuantumGravityBrstCharge.affMat_close
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:39:10.102335+00:00
-- url     : https://prove2.me/theorems/c6d0ebb9-85b9-4b5c-b9e5-37ea9ef26f7e
-- title:
--   `BookProof.QuantumGravityBrstCharge.affMat_close` (a b : Fin 19) : affMat a * affMat b - affMat b * affMat a = ∑ e, affF a b e • affMat e
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.affMat_close` (a b : Fin 19) : affMat a * affMat b - affMat b * affMat a = ∑ e, affF a b e • affMat e
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.affMat_close`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.affMat_close
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}

theorem BookProof.QuantumGravityBrstCharge.affMat_close (a b : Fin 19) :
    affMat a * affMat b - affMat b * affMat a = ∑ e, affF a b e • affMat e := by sorry
