-- Prove2me | Theorems.Thm_BookProof_ChapterWeylSl2_Sl2Rep_weyl_complete_reducibility
-- name    : BookProof.ChapterWeylSl2.Sl2Rep.weyl_complete_reducibility
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T23:19:42.993069+00:00
-- url     : https://prove2.me/theorems/0fe55894-6e88-4247-b6ea-cf7e77a37064
-- title:
--   `BookProof.ChapterWeylSl2.Sl2Rep.weyl_complete_reducibility` [FiniteDimensional ℂ V] (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) : ∃ W' : Submodule ℂ V, R.IsInv W' ∧ IsComp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterWeylSl2`.
--
--   `BookProof.ChapterWeylSl2.Sl2Rep.weyl_complete_reducibility` [FiniteDimensional ℂ V] (R : Sl2Rep V) (W : Submodule ℂ V) (hW : R.IsInv W) : ∃ W' : Submodule ℂ V, R.IsInv W' ∧ IsCompl W W'
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterWeylSl2.Sl2Rep.weyl_complete_reducibility`.

-- Generated from ChapterWeylSl2.lean — theorem BookProof.ChapterWeylSl2.Sl2Rep.weyl_complete_reducibility
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

theorem BookProof.ChapterWeylSl2.Sl2Rep.weyl_complete_reducibility [FiniteDimensional ℂ V] (R : Sl2Rep V) (W : Submodule ℂ V)
    (hW : R.IsInv W) : ∃ W' : Submodule ℂ V, R.IsInv W' ∧ IsCompl W W' := by sorry
