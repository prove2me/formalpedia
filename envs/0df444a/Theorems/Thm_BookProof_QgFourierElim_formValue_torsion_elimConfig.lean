-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_formValue_torsion_elimConfig
-- name    : BookProof.QgFourierElim.formValue_torsion_elimConfig
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T18:30:46.667975+00:00
-- url     : https://prove2.me/theorems/2dfdaee9-cbca-43ad-9335-3af91a35ddcd
-- title:
--   `BookProof.QgFourierElim.formValue_torsion_elimConfig` (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) : formValue k (torsionF mu nu i) (elimConfig k z) = Complex.I * (((k mu :
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.formValue_torsion_elimConfig` (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) : formValue k (torsionF mu nu i) (elimConfig k z) = Complex.I * (((k mu : ℤ) : ℂ) * z (nu, i) - ((k nu : ℤ) : ℂ) * z (mu, i))
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.formValue_torsion_elimConfig`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.formValue_torsion_elimConfig
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterQgContinuumModeInstance
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterA4
import Mathlib
import Definitions.Def_ChapterQgFourierElimination
import Definitions.Def_ChapterQgOuterFockFlow
import Definitions.Def_ChapterQgFourierElimForms



open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.QgVielbeinModeInstance BookProof.QgContinuumModeInstance
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

theorem BookProof.QgFourierElim.formValue_torsion_elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) :
    formValue k (torsionF mu nu i) (elimConfig k z)
      = Complex.I * (((k mu : ℤ) : ℂ) * z (nu, i) - ((k nu : ℤ) : ℂ) * z (mu, i)) := by sorry
