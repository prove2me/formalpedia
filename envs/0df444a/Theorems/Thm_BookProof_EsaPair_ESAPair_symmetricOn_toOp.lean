-- Prove2me | Theorems.Thm_BookProof_EsaPair_ESAPair_symmetricOn_toOp
-- name    : BookProof.EsaPair.ESAPair.symmetricOn_toOp
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:33.709063+00:00
-- url     : https://prove2.me/theorems/7bab83a2-225e-4231-92af-6eb03ba06ae3
-- title:
--   `BookProof.EsaPair.ESAPair.symmetricOn_toOp` : SymmetricOn P.coreDomain P.toOp
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEsaPairDGamma`.
--
--   `BookProof.EsaPair.ESAPair.symmetricOn_toOp` : SymmetricOn P.coreDomain P.toOp
--
--   Formalization note: Lean 4 identifier `BookProof.EsaPair.ESAPair.symmetricOn_toOp`.

-- Generated from ChapterEsaPairDGamma.lean — theorem BookProof.EsaPair.ESAPair.symmetricOn_toOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStoneConverse
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterShiftedQuadraticEsa
open BookProof.ChapterStoneMeasurable
open BookProof.ChapterStoneMeasurable.WeakMeasurableUnitaryGroup
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem BookProof.EsaPair.ESAPair.symmetricOn_toOp : SymmetricOn P.coreDomain P.toOp := by sorry
