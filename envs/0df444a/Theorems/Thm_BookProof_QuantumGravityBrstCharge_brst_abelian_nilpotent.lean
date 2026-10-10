-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_brst_abelian_nilpotent
-- name    : BookProof.QuantumGravityBrstCharge.brst_abelian_nilpotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:36:04.521021+00:00
-- url     : https://prove2.me/theorems/6150f53f-a391-4257-8116-7c15403d9eeb
-- title:
--   `BookProof.QuantumGravityBrstCharge.brst_abelian_nilpotent` (hCAR : GhostCAR χ β) (hcomm_chi : ∀ a b, G a * χ b = χ b * G a) (hcomm_beta : ∀ a b, G a * β b = β b * G a) (hab : ∀ a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.brst_abelian_nilpotent` (hCAR : GhostCAR χ β) (hcomm_chi : ∀ a b, G a * χ b = χ b * G a) (hcomm_beta : ∀ a b, G a * β b = β b * G a) (hab : ∀ a b, G a * G b = G b * G a) : glin G χ * glin G χ = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.brst_abelian_nilpotent`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.brst_abelian_nilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterBRSTNilpotent
open BookProof.BRSTNilpotent
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}

theorem BookProof.QuantumGravityBrstCharge.brst_abelian_nilpotent (hCAR : GhostCAR χ β)
    (hcomm_chi : ∀ a b, G a * χ b = χ b * G a) (hcomm_beta : ∀ a b, G a * β b = β b * G a)
    (hab : ∀ a b, G a * G b = G b * G a) :
    glin G χ * glin G χ = 0 := by sorry
