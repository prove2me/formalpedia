-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_affF_contract
-- name    : BookProof.QuantumGravityBrstCharge.affF_contract
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:39:04.055094+00:00
-- url     : https://prove2.me/theorems/70d15386-2694-4eaf-87bd-9101c934a927
-- title:
--   `BookProof.QuantumGravityBrstCharge.affF_contract` (x y z w : Fin 19) : ∑ e, affF x y e * affF e z w = affEps x y * (if w = 1 then affEps 1 z else 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.affF_contract` (x y z w : Fin 19) : ∑ e, affF x y e * affF e z w = affEps x y * (if w = 1 then affEps 1 z else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.affF_contract`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.affF_contract
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

theorem BookProof.QuantumGravityBrstCharge.affF_contract (x y z w : Fin 19) :
    ∑ e, affF x y e * affF e z w = affEps x y * (if w = 1 then affEps 1 z else 0) := by sorry
