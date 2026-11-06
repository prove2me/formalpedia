-- Prove2me | Theorems.Thm_BookProof_EsaPair_ESAPair_dGamma_symmetricOn
-- name    : BookProof.EsaPair.ESAPair.dGamma_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:55.470182+00:00
-- url     : https://prove2.me/theorems/af5a14e1-b535-4a83-b81d-77d4f3159594
-- title:
--   `BookProof.EsaPair.ESAPair.dGamma_symmetricOn` : SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n)) P.dGammaOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEsaPairDGamma`.
--
--   `BookProof.EsaPair.ESAPair.dGamma_symmetricOn` : SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n)) P.dGammaOp
--
--   Formalization note: Lean 4 identifier `BookProof.EsaPair.ESAPair.dGamma_symmetricOn`.

-- Generated from ChapterEsaPairDGamma.lean — theorem BookProof.EsaPair.ESAPair.dGamma_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterFockSecondQuantization
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSirkBandLedger
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.DirectSumEsa
open BookProof.FockSecondQuantization
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair
open BookProof.SecondQuantizationCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem BookProof.EsaPair.ESAPair.dGamma_symmetricOn :
    SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n))
      P.dGammaOp := by sorry
