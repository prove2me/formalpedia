-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_formValue_dGauge_elimConfig
-- name    : BookProof.QgFourierElim.formValue_dGauge_elimConfig
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T18:28:57.68621+00:00
-- url     : https://prove2.me/theorems/03afa7db-22e2-4ff9-b8b4-f81724431cf5
-- title:
--   `BookProof.QgFourierElim.formValue_dGauge_elimConfig` (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) : formValue k (dGaugeF mu nu i) (elimConfig k z) = 0
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.formValue_dGauge_elimConfig` (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) : formValue k (dGaugeF mu nu i) (elimConfig k z) = 0
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.formValue_dGauge_elimConfig`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.formValue_dGauge_elimConfig
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

theorem BookProof.QgFourierElim.formValue_dGauge_elimConfig (k : Mom) (z : Fin 3 × Fin 3 → ℂ) (mu nu i : Fin 3) :
    formValue k (dGaugeF mu nu i) (elimConfig k z) = 0 := by sorry
