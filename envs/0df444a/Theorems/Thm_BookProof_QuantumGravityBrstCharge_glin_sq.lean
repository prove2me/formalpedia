-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_glin_sq
-- name    : BookProof.QuantumGravityBrstCharge.glin_sq
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:35:24.835325+00:00
-- url     : https://prove2.me/theorems/81a01b56-50b7-43f1-92b8-1665a46b4d40
-- title:
--   `BookProof.QuantumGravityBrstCharge.glin_sq` (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) : glin G χ * glin G χ = (1 / 2 : ℝ) • ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.glin_sq` (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) : glin G χ * glin G χ = (1 / 2 : ℝ) • ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ b))
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.glin_sq`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.glin_sq
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterFreeFieldConstraint
open BookProof.BRSTNilpotent
open BookProof.FreeFieldConstraint
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}

theorem BookProof.QuantumGravityBrstCharge.glin_sq (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) :
    glin G χ * glin G χ = (1 / 2 : ℝ) • ∑ a, ∑ b, ∑ e, f a b e • (G e * (χ a * χ b)) := by sorry
