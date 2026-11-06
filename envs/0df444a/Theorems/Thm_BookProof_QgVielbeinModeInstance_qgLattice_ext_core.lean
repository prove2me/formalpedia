-- Prove2me | Theorems.Thm_BookProof_QgVielbeinModeInstance_qgLattice_ext_core
-- name    : BookProof.QgVielbeinModeInstance.qgLattice_ext_core
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-05T13:11:40.2372+00:00
-- url     : https://prove2.me/theorems/9252ef25-1ab2-45cb-a537-7c654b453c81
-- title:
--   `BookProof.QgVielbeinModeInstance.qgLattice_ext_core` (W : WallPot) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) (p : secCore (ι
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgVielbeinModeInstance`.
--
--   `BookProof.QgVielbeinModeInstance.qgLattice_ext_core` (W : WallPot) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ) (p : secCore (ι
--
--   Formalization note: Lean 4 identifier `BookProof.QgVielbeinModeInstance.qgLattice_ext_core`.

-- Generated from ChapterQgVielbeinModeInstance.lean — theorem BookProof.QgVielbeinModeInstance.qgLattice_ext_core
import Definitions.Def_ChapterScalaronOuterFockFL
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterQgVielbeinModeInstance
import Definitions.Def_ChapterQgOuterFockCoreFL
import Definitions.Def_ChapterScalaronFiberFL
open BookProof.QgOuterFockCoreFL
open BookProof.QgOuterFockCoreFL.CoreData
open BookProof.ScalaronFiberFL
open BookProof.ScalaronFiberFL.WallPot
open BookProof.QgVielbeinModeInstance



open BookProof.ScalaronFiberFL BookProof.ScalaronOuterFockFL
open BookProof.FarisLavine BookProof.QgOuterFockCoreFL

noncomputable section

variable {ι : Type*}

variable [Fintype ι] [DecidableEq ι]
variable (L : ℕ) [NeZero L]

theorem BookProof.QgVielbeinModeInstance.qgLattice_ext_core (W : WallPot) (sig : VMode L → ℝ) (hsig : ∀ a, 1 ≤ sig a) (g : ℝ)
    (p : secCore (ι := VMode L)) :
    (secData W (qgLatticeModes L sig hsig g)).ext
        ⟨(p : Sec (VMode L)), (secData W (qgLatticeModes L sig hsig g)).gc.le p.2⟩
      = secHam W (qgLatticeModes L sig hsig g) p := by sorry
