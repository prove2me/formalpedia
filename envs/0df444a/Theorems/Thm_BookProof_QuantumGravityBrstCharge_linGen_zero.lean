-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_zero
-- name    : BookProof.QuantumGravityBrstCharge.linGen_zero
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:09.290328+00:00
-- url     : https://prove2.me/theorems/654d9996-4f21-440b-a265-1c19677ff5b8
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_zero` : linGen (0 : Matrix (Fin d) (Fin d) ℝ) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_zero` : linGen (0 : Matrix (Fin d) (Fin d) ℝ) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_zero`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_zero
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

theorem BookProof.QuantumGravityBrstCharge.linGen_zero : linGen (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by sorry
