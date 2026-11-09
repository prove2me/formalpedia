-- Prove2me | Theorems.Thm_BookProof_FockSchur_hop_essentiallySelfAdjointOn_core
-- name    : BookProof.FockSchur.hop_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T08:03:24.311196+00:00
-- url     : https://prove2.me/theorems/3e59b1dd-bb6a-4813-9bfd-a5dce8d2028b
-- title:
--   `BookProof.FockSchur.hop_essentiallySelfAdjointOn_core` : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp hopCol)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockSchurEsa`.
--
--   `BookProof.FockSchur.hop_essentiallySelfAdjointOn_core` : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp hopCol)
--
--   Formalization note: Lean 4 identifier `BookProof.FockSchur.hop_essentiallySelfAdjointOn_core`.

-- Generated from ChapterFockSchurEsa.lean — theorem BookProof.FockSchur.hop_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterYangMillsFriedrichs
import Mathlib
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterFockWeightedSchurEsa
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.FockSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent
open BookProof.YangMillsFriedrichs

noncomputable section

variable {col : ℕ → (ℕ →₀ ℂ)} {K : ℝ}

theorem BookProof.FockSchur.hop_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp hopCol) := by sorry
