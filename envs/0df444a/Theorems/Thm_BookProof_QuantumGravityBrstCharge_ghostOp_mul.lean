-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_ghostOp_mul
-- name    : BookProof.QuantumGravityBrstCharge.ghostOp_mul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:37:23.806201+00:00
-- url     : https://prove2.me/theorems/f47f9926-99b2-4ac6-a2c8-24fe76d62928
-- title:
--   `BookProof.QuantumGravityBrstCharge.ghostOp_mul` (S T : Module.End ℂ ghostSpace) : ghostOp (S * T) = ghostOp S * ghostOp T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.ghostOp_mul` (S T : Module.End ℂ ghostSpace) : ghostOp (S * T) = ghostOp S * ghostOp T
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.ghostOp_mul`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.ghostOp_mul
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

theorem BookProof.QuantumGravityBrstCharge.ghostOp_mul (S T : Module.End ℂ ghostSpace) : ghostOp (S * T) = ghostOp S * ghostOp T := by sorry
