-- Prove2me | Theorems.Thm_BookProof_NsFullLagrangian_lagFullFockHam_sector
-- name    : BookProof.NsFullLagrangian.lagFullFockHam_sector
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-03T22:24:55.021636+00:00
-- url     : https://prove2.me/theorems/e041d9b6-015e-4ac6-a303-96f37439d79d
-- title:
--   `BookProof.NsFullLagrangian.lagFullFockHam_sector` (lam lam' mu gg : ℝ) (x : lagFockCore) (n : ℕ) : ((lagFullFockHam lam lam' mu gg x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n = l
-- statement:
--   Prove the following Lean 4 theorem from `ChapterNavierStokesFullLagrangianFock`.
--
--   `BookProof.NsFullLagrangian.lagFullFockHam_sector` (lam lam' mu gg : ℝ) (x : lagFockCore) (n : ℕ) : ((lagFullFockHam lam lam' mu gg x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n = lagSectorHam lam lam' mu gg n ⟨((x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n, x.2.2 n⟩
--
--   Formalization note: Lean 4 identifier `BookProof.NsFullLagrangian.lagFullFockHam_sector`.

-- Generated from ChapterNavierStokesFullLagrangianFock.lean — theorem BookProof.NsFullLagrangian.lagFullFockHam_sector
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterQgOuterFockFarisLavine
import Definitions.Def_ChapterQgOuterFockInteractionFL
import Definitions.Def_ChapterQg3DGaugeFarisLavine
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterNavierStokesFullLagrangianFock
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGaussCoreQuadBounds
import Definitions.Def_ChapterLeafGaps
import Definitions.Def_ChapterQgOuterFockInteractionFL
open BookProof.HermiteProductCore



open MvPolynomial
open BookProof.YangMillsHermite BookProof.YangMillsFriedrichs BookProof.FriedrichsExtension
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.DirectSumEsa
open BookProof.QgOuterFock BookProof.StoneBridge BookProof.QgOuterFockFL
open BookProof.QgOuterFockInteractionFL
open BookProof.ChapterStoneResolvent

noncomputable section

variable {n : ℕ}

theorem BookProof.NsFullLagrangian.lagFullFockHam_sector (lam lam' mu gg : ℝ) (x : lagFockCore) (n : ℕ) :
    ((lagFullFockHam lam lam' mu gg x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n
      = lagSectorHam lam lam' mu gg n
        ⟨((x : lagFockSpace) : ∀ n : ℕ, L2d (n * 36)) n, x.2.2 n⟩ := by sorry
