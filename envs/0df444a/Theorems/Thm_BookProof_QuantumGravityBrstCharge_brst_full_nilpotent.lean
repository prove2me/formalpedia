-- Prove2me | Theorems.Thm_BookProof_QuantumGravityBrstCharge_brst_full_nilpotent
-- name    : BookProof.QuantumGravityBrstCharge.brst_full_nilpotent
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T10:35:42.061555+00:00
-- url     : https://prove2.me/theorems/193ad4cc-b337-4373-a03c-ff47c829555c
-- title:
--   `BookProof.QuantumGravityBrstCharge.brst_full_nilpotent` (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) (hf12 : ∀ a b c, f a b c = -f b a c) (hjac : ∀ a b c h : Fin n, ∑ e
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQuantumGravityBrstCharge`.
--
--   `BookProof.QuantumGravityBrstCharge.brst_full_nilpotent` (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β) (hf12 : ∀ a b c, f a b c = -f b a c) (hjac : ∀ a b c h : Fin n, ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) : brstCharge f G χ β * brstCharge f G χ β = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QuantumGravityBrstCharge.brst_full_nilpotent`.

-- Generated from ChapterQuantumGravityBrstCharge.lean — theorem BookProof.QuantumGravityBrstCharge.brst_full_nilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterSmBrstGhost
open BookProof.BRSTNilpotent
open BookProof.SmBrstGhost
open BookProof.QuantumGravityBrstCharge



open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}

theorem BookProof.QuantumGravityBrstCharge.brst_full_nilpotent (hCAR : GhostCAR χ β) (hCA : ConstraintAlgebra f G χ β)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    brstCharge f G χ β * brstCharge f G χ β = 0 := by sorry
