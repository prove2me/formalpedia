-- Prove2me | Theorems.Thm_BookProof_QgCouplingDGammaSum_numberOp_essentiallySelfAdjoint
-- name    : BookProof.QgCouplingDGammaSum.numberOp_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T10:20:25.092914+00:00
-- url     : https://prove2.me/theorems/8c03e2e1-289c-4fb9-9b73-2aba7fb34b06
-- title:
--   `BookProof.QgCouplingDGammaSum.numberOp_essentiallySelfAdjoint` : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp numberCol)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterQgCouplingDGammaSum`.
--
--   `BookProof.QgCouplingDGammaSum.numberOp_essentiallySelfAdjoint` : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp numberCol)
--
--   Formalization note: Lean 4 identifier `BookProof.QgCouplingDGammaSum.numberOp_essentiallySelfAdjoint`.

-- Generated from ChapterQgCouplingDGammaSum.lean — theorem BookProof.QgCouplingDGammaSum.numberOp_essentiallySelfAdjoint
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterQgCouplingDGammaSum
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockOneParticleGap
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
open BookProof.FockOneParticleGap
open BookProof.FockSecondQuantization
open BookProof.QgCouplingDGammaSum



open BookProof.FockSecondQuantization
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.YangMillsFriedrichs

noncomputable section

variable {ι : Type*}

theorem BookProof.QgCouplingDGammaSum.numberOp_essentiallySelfAdjoint :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp numberCol) := by sorry
