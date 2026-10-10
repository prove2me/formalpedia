-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_sum4_swap_blocks
-- name    : BookProof.QuantumGravityBrstCharge.sum4_swap_blocks
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:25.77898+00:00
-- url     : https://prove2.me/theorems/4ad25a09-357f-42d1-9f2f-83dd7670d421
-- title:
--   `BookProof.QuantumGravityBrstCharge.sum4_swap_blocks` [AddCommMonoid α] (F : Fin d → Fin d → Fin d → Fin d → α) : ∑ l, ∑ m, ∑ j, ∑ k, F l m j k = ∑ j, ∑ k, ∑ l, ∑ m, F l...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.sum4_swap_blocks` [AddCommMonoid α] (F : Fin d → Fin d → Fin d → Fin d → α) : ∑ l, ∑ m, ∑ j, ∑ k, F l m j k = ∑ j, ∑ k, ∑ l, ∑ m, F l m j k
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.sum4_swap_blocks`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.sum4_swap_blocks
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

theorem BookProof.QuantumGravityBrstCharge.sum4_swap_blocks [AddCommMonoid α] (F : Fin d → Fin d → Fin d → Fin d → α) :
    ∑ l, ∑ m, ∑ j, ∑ k, F l m j k = ∑ j, ∑ k, ∑ l, ∑ m, F l m j k := by sorry
