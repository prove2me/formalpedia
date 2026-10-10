-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_sum4_sub_distrib
-- name    : BookProof.QuantumGravityBrstCharge.sum4_sub_distrib
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:33.040988+00:00
-- url     : https://prove2.me/theorems/7b0f8609-eb38-41b7-ac63-d8dddce76d24
-- title:
--   `BookProof.QuantumGravityBrstCharge.sum4_sub_distrib` [AddCommGroup α] (F G : Fin d → Fin d → Fin d → Fin d → α) : (∑ j, ∑ k, ∑ l, ∑ m, F j k l m) - (∑ j, ∑ k, ∑ l, ∑ m,...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.sum4_sub_distrib` [AddCommGroup α] (F G : Fin d → Fin d → Fin d → Fin d → α) : (∑ j, ∑ k, ∑ l, ∑ m, F j k l m) - (∑ j, ∑ k, ∑ l, ∑ m, G j k l m) = ∑ j, ∑ k, ∑ l, ∑ m, (F j k l m - G j k l m)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.sum4_sub_distrib`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.sum4_sub_distrib
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

theorem BookProof.QuantumGravityBrstCharge.sum4_sub_distrib [AddCommGroup α] (F G : Fin d → Fin d → Fin d → Fin d → α) :
    (∑ j, ∑ k, ∑ l, ∑ m, F j k l m) - (∑ j, ∑ k, ∑ l, ∑ m, G j k l m)
      = ∑ j, ∑ k, ∑ l, ∑ m, (F j k l m - G j k l m) := by sorry
