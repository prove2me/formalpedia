-- Prove2me | Theorems.Thm_BookProof_FockWeightedSchur_osc_essentiallySelfAdjointOn_core
-- name    : BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-08T09:33:30.497026+00:00
-- url     : https://prove2.me/theorems/7726452c-4b4d-40d1-ab82-3703b4e6c4ed
-- title:
--   `BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core` : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp oscCol)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterFockWeightedSchurEsa`.
--
--   `BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core` : EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp oscCol)
--
--   Formalization note: Lean 4 identifier `BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core`.

-- Generated from ChapterFockWeightedSchurEsa.lean — theorem BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core
import Definitions.Def_ChapterCoreBoundsEsa
import Definitions.Def_ChapterFockSchurEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterFockWeightedSchurEsaPromoted
import Definitions.Def_ChapterSirkBandLedger
open BookProof.FockSecondQuantization
open BookProof.FockWeightedSchur



open BookProof.FockSecondQuantization BookProof.CoreBounds BookProof.FockSchur
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {w : ℕ → ℝ}
variable {col : ℕ → (ℕ →₀ ℂ)} {K B : ℝ}

theorem BookProof.FockWeightedSchur.osc_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp oscCol) := by sorry
