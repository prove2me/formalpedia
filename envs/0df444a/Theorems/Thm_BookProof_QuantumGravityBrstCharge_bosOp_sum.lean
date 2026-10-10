-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_sum
-- name    : BookProof.QuantumGravityBrstCharge.bosOp_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:37:24.318317+00:00
-- url     : https://prove2.me/theorems/6e917280-bf62-4956-9c37-81d02d7b7b0d
-- title:
--   `BookProof.QuantumGravityBrstCharge.bosOp_sum` {n : ℕ} (T : Fin n → Module.End ℂ qgPoly) : bosOp (∑ e, T e) = ∑ e, bosOp (T e)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.bosOp_sum` {n : ℕ} (T : Fin n → Module.End ℂ qgPoly) : bosOp (∑ e, T e) = ∑ e, bosOp (T e)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.bosOp_sum`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.bosOp_sum
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

theorem BookProof.QuantumGravityBrstCharge.bosOp_sum {n : ℕ} (T : Fin n → Module.End ℂ qgPoly) :
    bosOp (∑ e, T e) = ∑ e, bosOp (T e) := by sorry
