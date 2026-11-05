-- Prove2me | Theorems.Thm_BookProof_DiagonalDGamma_dGamma_diag_essentiallySelfAdjointOn_fockCore
-- name    : BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:56.832908+00:00
-- url     : https://prove2.me/theorems/32189274-4680-4bc1-8dcb-0e842bc0bb4b
-- title:
--   `BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore` (lam : ι → ℝ) (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier)) (D : Submodule ℂ Hs.carrie
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiagonalDGammaEsa`.
--
--   `BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore` (lam : ι → ℝ) (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier)) (D : Submodule ℂ Hs.carrier) (hcore : IsGraphCore D (diagOp hE lam)) : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs (diagDomain E) D n)) (dGammaCoreOp Hs (diagDomain E) (diagOp hE lam) D)
--
--   Formalization note: Lean 4 identifier `BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore`.

-- Generated from ChapterDiagonalDGammaEsa.lean — theorem BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDiagonalDGammaEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterGroupAverageEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.DirectSumEsa
open BookProof.GraphCore
open BookProof.TensorCore



open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore
open BookProof.SecondQuantizationCore

noncomputable section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  {ι : Type*} (e : ι → D₂) (lam : ι → ℝ)
variable {Hs}
variable {E : ι → Hs.carrier} (hE : Orthonormal ℂ E)

theorem BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore (lam : ι → ℝ)
    (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier))
    (D : Submodule ℂ Hs.carrier) (hcore : IsGraphCore D (diagOp hE lam)) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore Hs (diagDomain E) D n))
      (dGammaCoreOp Hs (diagDomain E) (diagOp hE lam) D) := by sorry
