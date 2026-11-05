-- Prove2me | Theorems.Thm_BookProof_EsaPair_ESAPair_dGamma_essentiallySelfAdjoint
-- name    : BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:46.268358+00:00
-- url     : https://prove2.me/theorems/8081a5b2-d84f-4235-a769-5fd7cb3b325c
-- title:
--   `BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint` : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n)) P.dGammaOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEsaPairDGamma`.
--
--   `BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint` : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n)) P.dGammaOp
--
--   Formalization note: Lean 4 identifier `BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint`.

-- Generated from ChapterEsaPairDGamma.lean — theorem BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.DirectSumEsa
open BookProof.FockSecondQuantization
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair
open BookProof.SecondQuantizationCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem BookProof.EsaPair.ESAPair.dGamma_essentiallySelfAdjoint :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n)) P.dGammaOp := by sorry
