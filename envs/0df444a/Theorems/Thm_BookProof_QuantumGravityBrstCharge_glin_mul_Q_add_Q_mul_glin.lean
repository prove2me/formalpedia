-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_glin_mul_Q_add_Q_mul_glin
-- name    : BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:35:32.797473+00:00
-- url     : https://prove2.me/theorems/2f1e55f2-e33e-4bec-85c6-3511de5c4913
-- title:
--   `BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin` (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) : glin G χ * Q f χ β + Q f χ β * glin G χ = ∑ d, ∑ g, ∑ h, f
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin` (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) : glin G χ * Q f χ β + Q f χ β * glin G χ = ∑ d, ∑ g, ∑ h, f d g h • (G h * (χ d * χ g))
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin
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

theorem BookProof.QuantumGravityBrstCharge.glin_mul_Q_add_Q_mul_glin (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) :
    glin G χ * Q f χ β + Q f χ β * glin G χ
      = ∑ d, ∑ g, ∑ h, f d g h • (G h * (χ d * χ g)) := by sorry
