-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_affF_antisymm
-- name    : BookProof.QuantumGravityBrstCharge.affF_antisymm
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:38:35.88193+00:00
-- url     : https://prove2.me/theorems/998c0a7d-bc35-434f-8b2f-53fed8731587
-- title:
--   `BookProof.QuantumGravityBrstCharge.affF_antisymm` (a b c : Fin 19) : affF a b c = -affF b a c
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.affF_antisymm` (a b c : Fin 19) : affF a b c = -affF b a c
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.affF_antisymm`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.affF_antisymm
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

theorem BookProof.QuantumGravityBrstCharge.affF_antisymm (a b c : Fin 19) : affF a b c = -affF b a c := by sorry
