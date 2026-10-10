-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_affBRST_nilpotent
-- name    : BookProof.QuantumGravityBrstCharge.affBRST_nilpotent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:39:24.645948+00:00
-- url     : https://prove2.me/theorems/c9cf583e-ff58-4ca9-b15b-5356aadfcf02
-- title:
--   `BookProof.QuantumGravityBrstCharge.affBRST_nilpotent` : qgBRST affMat affF * qgBRST affMat affF = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.affBRST_nilpotent` : qgBRST affMat affF * qgBRST affMat affF = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.affBRST_nilpotent`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.affBRST_nilpotent
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

theorem BookProof.QuantumGravityBrstCharge.affBRST_nilpotent : qgBRST affMat affF * qgBRST affMat affF = 0 := by sorry
