-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_affF_jacobi
-- name    : BookProof.QuantumGravityBrstCharge.affF_jacobi
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:38:51.6415+00:00
-- url     : https://prove2.me/theorems/63b96508-b5a1-4d9b-8514-9a11e4a77dc7
-- title:
--   `BookProof.QuantumGravityBrstCharge.affF_jacobi` (a b c h : Fin 19) : ∑ e, (affF a b e * affF e c h + affF b c e * affF e a h + affF c a e * affF e b h) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.affF_jacobi` (a b c h : Fin 19) : ∑ e, (affF a b e * affF e c h + affF b c e * affF e a h + affF c a e * affF e b h) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.affF_jacobi`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.affF_jacobi
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

theorem BookProof.QuantumGravityBrstCharge.affF_jacobi (a b c h : Fin 19) :
    ∑ e, (affF a b e * affF e c h + affF b c e * affF e a h + affF c a e * affF e b h) = 0 := by sorry
