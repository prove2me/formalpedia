-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_bracket
-- name    : BookProof.QuantumGravityBrstCharge.linGen_bracket
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T22:57:38.718326+00:00
-- url     : https://prove2.me/theorems/50e941c6-397c-469b-9d50-2d2cc9af8aca
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_bracket` (A B : Matrix (Fin d) (Fin d) ℝ) : linGen A * linGen B - linGen B * linGen A = linGen (A * B - B * A)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_bracket` (A B : Matrix (Fin d) (Fin d) ℝ) : linGen A * linGen B - linGen B * linGen A = linGen (A * B - B * A)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_bracket`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_bracket
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

theorem BookProof.QuantumGravityBrstCharge.linGen_bracket (A B : Matrix (Fin d) (Fin d) ℝ) :
    linGen A * linGen B - linGen B * linGen A = linGen (A * B - B * A) := by sorry
