-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_formValue_gauge3d_elimConfig
-- name    : BookProof.QgFourierElim.formValue_gauge3d_elimConfig
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T18:33:52.002172+00:00
-- url     : https://prove2.me/theorems/ecfd86ee-bfc3-4985-a921-53c1d670d4a2
-- title:
--   `BookProof.QgFourierElim.formValue_gauge3d_elimConfig` (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (i : Fin 3) : formValue k (gauge3dF i) (elimConfig k z) = ∑ mu : Fin 3, Complex.I * ((k mu
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.formValue_gauge3d_elimConfig` (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (i : Fin 3) : formValue k (gauge3dF i) (elimConfig k z) = ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * z (mu, i)
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.formValue_gauge3d_elimConfig`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.formValue_gauge3d_elimConfig
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

theorem BookProof.QgFourierElim.formValue_gauge3d_elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    formValue k (gauge3dF i) (elimConfig k z)
      = ∑ mu : Fin 3, Complex.I * ((k mu : ℤ) : ℂ) * z (mu, i) := by sorry
