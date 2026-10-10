-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_contract_right
-- name    : BookProof.QuantumGravityBrstCharge.linGen_contract_right
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:51.302974+00:00
-- url     : https://prove2.me/theorems/0ad8017b-08e0-4b94-b9d6-6d83604744df
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_contract_right` (A B : Matrix (Fin d) (Fin d) ℝ) : (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if j = m then elemGen l k else 0)) = linGen (B
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_contract_right` (A B : Matrix (Fin d) (Fin d) ℝ) : (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if j = m then elemGen l k else 0)) = linGen (B * A)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_contract_right`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_contract_right
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

theorem BookProof.QuantumGravityBrstCharge.linGen_contract_right (A B : Matrix (Fin d) (Fin d) ℝ) :
    (∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (if j = m then elemGen l k else 0))
      = linGen (B * A) := by sorry
