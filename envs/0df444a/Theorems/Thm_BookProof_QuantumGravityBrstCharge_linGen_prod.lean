-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_prod
-- name    : BookProof.QuantumGravityBrstCharge.linGen_prod
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:42.275253+00:00
-- url     : https://prove2.me/theorems/95fc9035-764e-4aa9-a534-0f2b0dd68bcc
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_prod` (A B : Matrix (Fin d) (Fin d) ℝ) : linGen A * linGen B = ∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (elemGen j k * elemGen l m)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_prod` (A B : Matrix (Fin d) (Fin d) ℝ) : linGen A * linGen B = ∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (elemGen j k * elemGen l m)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_prod`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_prod
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

theorem BookProof.QuantumGravityBrstCharge.linGen_prod (A B : Matrix (Fin d) (Fin d) ℝ) :
    linGen A * linGen B
      = ∑ j, ∑ k, ∑ l, ∑ m, (A j k * B l m) • (elemGen j k * elemGen l m) := by sorry
