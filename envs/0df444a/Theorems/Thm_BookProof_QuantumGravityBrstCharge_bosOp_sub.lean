-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_sub
-- name    : BookProof.QuantumGravityBrstCharge.bosOp_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:37:28.599674+00:00
-- url     : https://prove2.me/theorems/3dfefd8b-a816-42ec-b1d5-5e3e669d0843
-- title:
--   `BookProof.QuantumGravityBrstCharge.bosOp_sub` (S T : Module.End ℂ qgPoly) : bosOp (S - T) = bosOp S - bosOp T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.bosOp_sub` (S T : Module.End ℂ qgPoly) : bosOp (S - T) = bosOp S - bosOp T
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.bosOp_sub`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.bosOp_sub
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

theorem BookProof.QuantumGravityBrstCharge.bosOp_sub (S T : Module.End ℂ qgPoly) : bosOp (S - T) = bosOp S - bosOp T := by sorry
