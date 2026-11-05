-- Prove2me | Theorems.Thm_BookProof_EsaPair_ESAPair_norm_sub_smul_sq
-- name    : BookProof.EsaPair.ESAPair.norm_sub_smul_sq
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:53:05.782691+00:00
-- url     : https://prove2.me/theorems/ea06665e-95d9-41fa-9661-1762ff133a63
-- title:
--   `BookProof.EsaPair.ESAPair.norm_sub_smul_sq` (d : ℝ) (x : P.coreDomain) : ‖P.toOp x - ((d : ℂ) * Complex.I) • (x : Hs.carrier)‖ ^ 2 = ‖P.toOp x‖ ^ 2 + d ^ 2 * ‖(x : Hs.carrier)‖ ^
-- statement:
--   Prove the following Lean 4 theorem from `ChapterEsaPairDGamma`.
--
--   `BookProof.EsaPair.ESAPair.norm_sub_smul_sq` (d : ℝ) (x : P.coreDomain) : ‖P.toOp x - ((d : ℂ) * Complex.I) • (x : Hs.carrier)‖ ^ 2 = ‖P.toOp x‖ ^ 2 + d ^ 2 * ‖(x : Hs.carrier)‖ ^ 2
--
--   Formalization note: Lean 4 identifier `BookProof.EsaPair.ESAPair.norm_sub_smul_sq`.

-- Generated from ChapterEsaPairDGamma.lean — theorem BookProof.EsaPair.ESAPair.norm_sub_smul_sq
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterEsaPairDGamma
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterPermutationSectorEsa
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.EsaPair

noncomputable section

variable {Hs : IPSpace} (P : ESAPair Hs)

theorem BookProof.EsaPair.ESAPair.norm_sub_smul_sq (d : ℝ) (x : P.coreDomain) :
    ‖P.toOp x - ((d : ℂ) * Complex.I) • (x : Hs.carrier)‖ ^ 2
      = ‖P.toOp x‖ ^ 2 + d ^ 2 * ‖(x : Hs.carrier)‖ ^ 2 := by sorry
