-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_elemGen_bracket
-- name    : BookProof.QuantumGravityBrstCharge.elemGen_bracket
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:46:27.181118+00:00
-- url     : https://prove2.me/theorems/690d2515-0b0d-45e8-8b7a-d8eed80cc7ac
-- title:
--   `BookProof.QuantumGravityBrstCharge.elemGen_bracket` (j k l m : Fin d) : elemGen j k * elemGen l m - elemGen l m * elemGen j k = (if k = l then elemGen j m else 0) - (if j = m then
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.elemGen_bracket` (j k l m : Fin d) : elemGen j k * elemGen l m - elemGen l m * elemGen j k = (if k = l then elemGen j m else 0) - (if j = m then elemGen l k else 0)
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.elemGen_bracket`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.elemGen_bracket
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

theorem BookProof.QuantumGravityBrstCharge.elemGen_bracket (j k l m : Fin d) :
    elemGen j k * elemGen l m - elemGen l m * elemGen j k
      = (if k = l then elemGen j m else 0) - (if j = m then elemGen l k else 0) := by sorry
