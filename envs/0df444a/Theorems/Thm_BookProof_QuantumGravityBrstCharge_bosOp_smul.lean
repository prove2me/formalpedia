-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_bosOp_smul
-- name    : BookProof.QuantumGravityBrstCharge.bosOp_smul
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:37:13.006702+00:00
-- url     : https://prove2.me/theorems/c049e663-020f-4acb-b044-d923b5c83fc5
-- title:
--   `BookProof.QuantumGravityBrstCharge.bosOp_smul` (r : ℝ) (T : Module.End ℂ qgPoly) : bosOp (r • T) = r • bosOp T
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.bosOp_smul` (r : ℝ) (T : Module.End ℂ qgPoly) : bosOp (r • T) = r • bosOp T
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.bosOp_smul`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.bosOp_smul
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

theorem BookProof.QuantumGravityBrstCharge.bosOp_smul (r : ℝ) (T : Module.End ℂ qgPoly) : bosOp (r • T) = r • bosOp T := by sorry
