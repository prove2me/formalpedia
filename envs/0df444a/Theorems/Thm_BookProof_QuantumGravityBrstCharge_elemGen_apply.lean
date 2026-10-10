-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_elemGen_apply
-- name    : BookProof.QuantumGravityBrstCharge.elemGen_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:58.419996+00:00
-- url     : https://prove2.me/theorems/1a96dfce-e55f-4184-804d-9b4f57d99e4a
-- title:
--   `BookProof.QuantumGravityBrstCharge.elemGen_apply` (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) : elemGen j k p = X j * derOp k p
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.elemGen_apply` (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) : elemGen j k p = X j * derOp k p
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.elemGen_apply`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.elemGen_apply
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}

theorem BookProof.QuantumGravityBrstCharge.elemGen_apply (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    elemGen j k p = X j * derOp k p := by sorry
