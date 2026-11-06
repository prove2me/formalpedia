-- Prove2me | Theorems.Thm_BookProof_DiagonalDGamma_dGamma_diag_essentiallySelfAdjointOn_fockCore_self
-- name    : BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-11-04T22:52:27.078236+00:00
-- url     : https://prove2.me/theorems/a95f78d9-1709-4741-b967-82e5eb0b58c5
-- title:
--   `BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self` (lam : ι → ℝ) (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier)) : EssentiallySelfAdjo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDiagonalDGammaEsa`.
--
--   `BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self` (lam : ι → ℝ) (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier)) : EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs (diagDomain E) (diagDomain E) n)) (dGammaCoreOp Hs (diagDomain E) (diagOp hE lam) (diagDomain E))
--
--   Formalization note: Lean 4 identifier `BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self`.

-- Generated from ChapterDiagonalDGammaEsa.lean — theorem BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Mathlib
import Definitions.Def_ChapterDiagonalDGammaEsa
import Definitions.Def_ChapterAbelianDiagonalCountable
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterTensorGraphCore
import Definitions.Def_ChapterAbelianAtomicCondensation
import Definitions.Def_ChapterBddBelowFiberSumEsa
import Definitions.Def_ChapterPermutationSectorEsa
import Definitions.Def_ChapterSecondQuantizationCoreEsa
open BookProof.ChapterAbelianDiagonalCountable
open BookProof.DirectSumEsa
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

theorem BookProof.DiagonalDGamma.dGamma_diag_essentiallySelfAdjointOn_fockCore_self (lam : ι → ℝ)
    (hdense : Dense (Submodule.span ℂ (Set.range E) : Set Hs.carrier)) :
    EssentiallySelfAdjointOn
      (dsCore (fun n : ℕ => fockSectorCore Hs (diagDomain E) (diagDomain E) n))
      (dGammaCoreOp Hs (diagDomain E) (diagOp hE lam) (diagDomain E)) := by sorry
