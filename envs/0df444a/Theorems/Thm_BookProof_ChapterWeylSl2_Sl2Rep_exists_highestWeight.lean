-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_exists_highestWeight
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T17:50:16.534993+00:00
-- url     : https://prove2.me/theorems/e8d732d6-fad8-4a1f-861a-d9e8978725cf
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight` [FiniteDimensional ℂ V] [Nontrivial V] (R : Sl2Rep V) : ∃ (w : V) (lam : ℂ), w ≠ 0 ∧ R.E w = 0 ∧ R.H w = lam • w
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight` [FiniteDimensional ℂ V] [Nontrivial V] (R : Sl2Rep V) : ∃ (w : V) (lam : ℂ), w ≠ 0 ∧ R.E w = 0 ∧ R.H w = lam • w
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight
import Mathlib
import Definitions.Def_ChapterWeylSl2
import Definitions.Def_ChapterDoubleSlit
import Definitions.Def_ChapterGleasonPureMixed
open BookProof.ChapterDoubleSlit
open BookProof.ChapterGleasonPureMixed
open BookProof.ChapterWeylSl2
open BookProof.ChapterWeylSl2



universe u

variable {V : Type u} [AddCommGroup V] [Module ℂ V]

variable (R : Sl2Rep V)
variable {R}
variable {R : Sl2Rep V}

theorem BookProof.ChapterWeylSl2.Sl2Rep.exists_highestWeight [FiniteDimensional ℂ V] [Nontrivial V] (R : Sl2Rep V) :
    ∃ (w : V) (lam : ℂ), w ≠ 0 ∧ R.E w = 0 ∧ R.H w = lam • w := by sorry
