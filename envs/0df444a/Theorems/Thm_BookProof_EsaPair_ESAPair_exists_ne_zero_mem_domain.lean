-- Prove2me | Theorems.Thm_BookProof_EsaPair_ESAPair_exists_ne_zero_mem_domain
-- name    : BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T23:38:42.412432+00:00
-- url     : https://prove2.me/theorems/5479954e-629d-40c2-b1ad-4886a8cef903
-- title:
--   `BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain` {a : Hs.carrier} (haD : a ∈ P.coreDomain) (ha0 : a ≠ 0) : ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreD
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEsaPairDGamma`.
--
--   `BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain` {a : Hs.carrier} (haD : a ∈ P.coreDomain) (ha0 : a ≠ 0) : ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n), f ≠ 0
--
--   Formalization note: Lean 4 identifier `BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain`.

-- Generated from ChapterEsaPairDGamma.lean — theorem BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.DirectSumEsa
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair
open BookProof.SecondQuantizationCore

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem BookProof.EsaPair.ESAPair.exists_ne_zero_mem_domain {a : Hs.carrier} (haD : a ∈ P.coreDomain)
    (ha0 : a ≠ 0) :
    ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs P.closureDomain P.coreDomain n), f ≠ 0 := by sorry
