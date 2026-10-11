-- Prove2me | Theorems.Thm_BookProof_SmBrstGhost_smBrstCharge_nilpotent
-- name    : BookProof.SmBrstGhost.smBrstCharge_nilpotent
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T13:26:39.557154+00:00
-- url     : https://prove2.me/theorems/a4314944-3b95-4375-b61c-ec06ceb1a645
-- title:
--   `BookProof.SmBrstGhost.smBrstCharge_nilpotent` {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} (hT : ClosesWithStructureConstants T (smStruct f3))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmBrstGhost`.
--
--   `BookProof.SmBrstGhost.smBrstCharge_nilpotent` {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ} {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} (hT : ClosesWithStructureConstants T (smStruct f3)) (h3anti : ∀ a b c, f3 a b c = -f3 b a c) (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h + f3 c a e * f3 e b h) = 0) : smBrstCharge m T f3 * smBrstCharge m T f3 = 0
--
--   Formalization note: Lean 4 identifier `BookProof.SmBrstGhost.smBrstCharge_nilpotent`.

-- Generated from ChapterSmBrstGhost.lean — theorem BookProof.SmBrstGhost.smBrstCharge_nilpotent
import Definitions.Def_ChapterBRSTNilpotent
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmCar
open BookProof.YangMillsSU3
open BookProof.SmBrstGhost



open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

theorem BookProof.SmBrstGhost.smBrstCharge_nilpotent {m : ℕ} {T : Fin 12 → Matrix (Fin m) (Fin m) ℂ}
    {f3 : Fin 8 → Fin 8 → Fin 8 → ℝ} (hT : ClosesWithStructureConstants T (smStruct f3))
    (h3anti : ∀ a b c, f3 a b c = -f3 b a c)
    (h3jac : ∀ a b c h : Fin 8, ∑ e, (f3 a b e * f3 e c h + f3 b c e * f3 e a h
      + f3 c a e * f3 e b h) = 0) :
    smBrstCharge m T f3 * smBrstCharge m T f3 = 0 := by sorry
