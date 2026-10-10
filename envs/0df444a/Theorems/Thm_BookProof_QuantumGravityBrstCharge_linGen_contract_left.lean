-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_contract_left
-- name    : BookProof.QuantumGravityBrstCharge.linGen_contract_left
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:47.291099+00:00
-- url     : https://prove2.me/theorems/6862d35f-7357-4688-a451-a9791e989ad0
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_contract_left` (A B : Matrix (Fin d) (Fin d) ℝ) : (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if k = l then elemGen j m else 0)) = linGen (A
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_contract_left` (A B : Matrix (Fin d) (Fin d) ℝ) : (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if k = l then elemGen j m else 0)) = linGen (A * B)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_contract_left`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_contract_left
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

theorem BookProof.QuantumGravityBrstCharge.linGen_contract_left (A B : Matrix (Fin d) (Fin d) ℝ) :
    (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if k = l then elemGen j m else 0))
      = linGen (A * B) := by sorry
