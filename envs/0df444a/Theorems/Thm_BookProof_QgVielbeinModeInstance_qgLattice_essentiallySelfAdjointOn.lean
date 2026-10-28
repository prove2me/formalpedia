-- Prove2me | Theorems.Thm_BookProof_QgVielbeinModeInstance_qgLattice_essentiallySelfAdjointOn
-- name    : BookProof.QgVielbeinModeInstance.qgLattice_essentiallySelfAdjointOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:37:49.351607+00:00
-- url     : https://prove2.me/theorems/f7113f44-af52-4fc6-943f-4a03d5c9db0c
-- title:
--   `BookProof.QgVielbeinModeInstance.qgLattice_essentiallySelfAdjointOn` (W : WallPot) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) : EssentiallySelfAdjointOn (secN W (qgLattic
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgVielbeinModeInstance`.
--
--   `BookProof.QgVielbeinModeInstance.qgLattice_essentiallySelfAdjointOn` (W : WallPot) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) : EssentiallySelfAdjointOn (secN W (qgLatticeModes L sig hsig g)).dom (secData W (qgLatticeModes L sig hsig g)).ext
--
--   Formalization note: Lean 4 identifier `BookProof.QgVielbeinModeInstance.qgLattice_essentiallySelfAdjointOn`.

-- Generated from ChapterQgVielbeinModeInstance.lean — theorem BookProof.QgVielbeinModeInstance.qgLattice_essentiallySelfAdjointOn
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

theorem BookProof.QgVielbeinModeInstance.qgLattice_essentiallySelfAdjointOn (W : WallPot) (sig : VMode L → ℝ)
    (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) :
    EssentiallySelfAdjointOn (secN W (qgLatticeModes L sig hsig g)).dom
      (secData W (qgLatticeModes L sig hsig g)).ext := by sorry
