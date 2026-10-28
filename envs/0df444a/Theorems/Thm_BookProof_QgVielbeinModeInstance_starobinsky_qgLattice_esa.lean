-- Prove2me | Theorems.Thm_BookProof_QgVielbeinModeInstance_starobinsky_qgLattice_esa
-- name    : BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:38:26.700058+00:00
-- url     : https://prove2.me/theorems/429615be-ecbd-4685-88eb-7dc73cbe3952
-- title:
--   `BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa` (M alpha : ℝ) (halpha : 0 < alpha) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) : EssentiallySelfAdjointOn (secN
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgVielbeinModeInstance`.
--
--   `BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa` (M alpha : ℝ) (halpha : 0 < alpha) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) : EssentiallySelfAdjointOn (secN (starobinskyWall M alpha halpha) (qgLatticeModes L sig hsig g)).dom (secData (starobinskyWall M alpha halpha) (qgLatticeModes L sig hsig g)).ext
--
--   Formalization note: Lean 4 identifier `BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa`.

-- Generated from ChapterQgVielbeinModeInstance.lean — theorem BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa
import Definitions.Def_ChapterScalaronFiberFL
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterQgOuterFockFlow
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.QgVielbeinModeInstance



open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

variable {ι : Type*}

variable [Fintype ι] [DecidableEq ι]
variable (L : ℕ) [NeZero L]

theorem BookProof.QgVielbeinModeInstance.starobinsky_qgLattice_esa (M alpha : ℝ) (halpha : 0 < alpha) (sig : VMode L → ℝ)
    (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) :
    EssentiallySelfAdjointOn
        (secN (starobinskyWall M alpha halpha) (qgLatticeModes L sig hsig g)).dom
      (secData (starobinskyWall M alpha halpha) (qgLatticeModes L sig hsig g)).ext := by sorry
