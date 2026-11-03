-- Prove2me | Theorems.Thm_BookProof_ScalarDGamma_dGamma_scalar_essentiallySelfAdjointOn_fockCore
-- name    : BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-02T13:16:17.135461+00:00
-- url     : https://prove2.me/theorems/a0851fd9-c017-4c7f-ac28-93259ead977f
-- title:
--   `BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore` {D : Submodule ℂ Hs.carrier} (hdense : Dense (D : Set Hs.carrier)) : EssentiallySelfAdjointOn (dsCore (fun
-- statement:
--   Prove the following Lean 4 theorem from `ChapterScalarDGammaEsa`.
--
--   `BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore` {D : Submodule ℂ Hs.carrier} (hdense : Dense (D : Set Hs.carrier)) : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n)) (dGammaCoreOp Hs ⊤ (scalarOp Hs c) D)
--
--   Formalization note: Lean 4 identifier `BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore`.

-- Generated from ChapterScalarDGammaEsa.lean — theorem BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterScalarDGammaEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.DirectSumEsa
open BookProof.TensorCore
open BookProof.ScalarDGamma



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable (Hs : IPSpace) (c : ℝ)

theorem BookProof.ScalarDGamma.dGamma_scalar_essentiallySelfAdjointOn_fockCore {D : Submodule ℂ Hs.carrier}
    (hdense : Dense (D : Set Hs.carrier)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs ⊤ D n))
      (dGammaCoreOp Hs ⊤ (scalarOp Hs c) D) := by sorry
