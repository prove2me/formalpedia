-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_affMat_non_abelian
-- name    : BookProof.QuantumGravityBrstCharge.affMat_non_abelian
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:38:30.95198+00:00
-- url     : https://prove2.me/theorems/fcb7729e-5014-40d5-8f5f-be6c9f68bf26
-- title:
--   `BookProof.QuantumGravityBrstCharge.affMat_non_abelian` : affMat 0 * affMat 1 ≠ affMat 1 * affMat 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.affMat_non_abelian` : affMat 0 * affMat 1 ≠ affMat 1 * affMat 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.affMat_non_abelian`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.affMat_non_abelian
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

theorem BookProof.QuantumGravityBrstCharge.affMat_non_abelian : affMat 0 * affMat 1 ≠ affMat 1 * affMat 0 := by sorry
