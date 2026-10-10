-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_smul_sum
-- name    : BookProof.QuantumGravityBrstCharge.linGen_smul_sum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:22.423115+00:00
-- url     : https://prove2.me/theorems/7276a8a2-0f20-450d-ab1f-e62f52fd1ac6
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_smul_sum` {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Matrix (Fin d) (Fin d) ℝ) : linGen (∑ e, c e • M e) = ∑ e, c e • linGen (M e)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_smul_sum` {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Matrix (Fin d) (Fin d) ℝ) : linGen (∑ e, c e • M e) = ∑ e, c e • linGen (M e)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_smul_sum`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_smul_sum
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

theorem BookProof.QuantumGravityBrstCharge.linGen_smul_sum {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    linGen (∑ e, c e • M e) = ∑ e, c e • linGen (M e) := by sorry
