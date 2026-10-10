-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_qgBRST_abelian_nilpotent
-- name    : BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:38:37.253047+00:00
-- url     : https://prove2.me/theorems/4967f7e4-06f2-40c5-b48c-cdd52f6a593e
-- title:
--   `BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent` (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ) (hcomm : ∀ a b, M a * M b = M b * M a) : glin (qgConstraint M) qgChi * glin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent` (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ) (hcomm : ∀ a b, M a * M b = M b * M a) : glin (qgConstraint M) qgChi * glin (qgConstraint M) qgChi = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}

theorem BookProof.QuantumGravityBrstCharge.qgBRST_abelian_nilpotent (M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ)
    (hcomm : ∀ a b, M a * M b = M b * M a) :
    glin (qgConstraint M) qgChi * glin (qgConstraint M) qgChi = 0 := by sorry
