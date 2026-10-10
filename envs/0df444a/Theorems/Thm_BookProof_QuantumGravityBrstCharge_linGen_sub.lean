-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_sub
-- name    : BookProof.QuantumGravityBrstCharge.linGen_sub
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:10.925161+00:00
-- url     : https://prove2.me/theorems/55583b4b-dc92-4837-8198-9c8cbd17c949
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_sub` (A B : Matrix (Fin d) (Fin d) ℝ) : linGen (A - B) = linGen A - linGen B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_sub` (A B : Matrix (Fin d) (Fin d) ℝ) : linGen (A - B) = linGen A - linGen B
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_sub`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_sub
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

theorem BookProof.QuantumGravityBrstCharge.linGen_sub (A B : Matrix (Fin d) (Fin d) ℝ) :
    linGen (A - B) = linGen A - linGen B := by sorry
