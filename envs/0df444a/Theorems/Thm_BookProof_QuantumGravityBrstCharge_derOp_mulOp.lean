-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_derOp_mulOp
-- name    : BookProof.QuantumGravityBrstCharge.derOp_mulOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:09:30.413985+00:00
-- url     : https://prove2.me/theorems/e7bae893-67fe-47b4-9aca-91362126a259
-- title:
--   `BookProof.QuantumGravityBrstCharge.derOp_mulOp` (k l : Fin d) (p : MvPolynomial (Fin d) ℂ) : derOp k (X l * p) = X l * derOp k p + (if k = l then p else 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.derOp_mulOp` (k l : Fin d) (p : MvPolynomial (Fin d) ℂ) : derOp k (X l * p) = X l * derOp k p + (if k = l then p else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.derOp_mulOp`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.derOp_mulOp
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}

theorem BookProof.QuantumGravityBrstCharge.derOp_mulOp (k l : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp k (X l * p) = X l * derOp k p + (if k = l then p else 0) := by sorry
