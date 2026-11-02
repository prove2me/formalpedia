-- Prove2me | Theorems.Thm_BookProof_QgFourierElim_eq_elimConfig_of_gauge_fixed
-- name    : BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-01T18:29:53.621605+00:00
-- url     : https://prove2.me/theorems/7c15c4ac-691c-4c93-8bfe-1cf60e165182
-- title:
--   `BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed` (k : Mom) (w : Comp → ℂ) (h : ∀ mu nu i, formValue k (dGaugeF mu nu i) w = 0) : w = elimConfig k (fun p => w (eIdx p.1 p.2))
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgFourierElimination`.
--
--   `BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed` (k : Mom) (w : Comp → ℂ) (h : ∀ mu nu i, formValue k (dGaugeF mu nu i) w = 0) : w = elimConfig k (fun p => w (eIdx p.1 p.2))
--
--   Formalization note: Lean 4 identifier `BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed`.

-- Generated from ChapterQgFourierElimination.lean — theorem BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed
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

theorem BookProof.QgFourierElim.eq_elimConfig_of_gauge_fixed (k : Mom) (w : Comp → ℂ)
    (h : ∀ mu nu i, formValue k (dGaugeF mu nu i) w = 0) :
    w = elimConfig k (fun p => w (eIdx p.1 p.2)) := by sorry
