-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_linGen_def
-- name    : BookProof.QuantumGravityBrstCharge.linGen_def
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:16.591835+00:00
-- url     : https://prove2.me/theorems/a8ccc6b8-ee6e-4ef6-95d8-65adff7033bf
-- title:
--   `BookProof.QuantumGravityBrstCharge.linGen_def` (M : Matrix (Fin d) (Fin d) ℝ) : linGen M = ∑ j, ∑ k, (M j k) • elemGen j k
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.linGen_def` (M : Matrix (Fin d) (Fin d) ℝ) : linGen M = ∑ j, ∑ k, (M j k) • elemGen j k
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.linGen_def`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.linGen_def
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

theorem BookProof.QuantumGravityBrstCharge.linGen_def (M : Matrix (Fin d) (Fin d) ℝ) :
    linGen M = ∑ j, ∑ k, (M j k) • elemGen j k := by sorry
