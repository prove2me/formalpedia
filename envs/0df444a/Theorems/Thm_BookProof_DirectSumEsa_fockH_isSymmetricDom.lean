-- Prove2me | Theorems.Thm_BookProof_DirectSumEsa_fockH_isSymmetricDom
-- name    : BookProof.DirectSumEsa.fockH_isSymmetricDom
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-27T05:19:03.187874+00:00
-- url     : https://prove2.me/theorems/ec1dcb4b-614b-4d68-a4c0-7fbfbcad89dd
-- title:
--   `BookProof.DirectSumEsa.fockH_isSymmetricDom` {w : ℝ → ℝ} (hw : Measurable w) : FullEsa.IsSymmetricDom (fockH hw)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterDirectSumEsa`.
--
--   `BookProof.DirectSumEsa.fockH_isSymmetricDom` {w : ℝ → ℝ} (hw : Measurable w) : FullEsa.IsSymmetricDom (fockH hw)
--
--   Formalization note: Lean 4 identifier `BookProof.DirectSumEsa.fockH_isSymmetricDom`.

-- Generated from ChapterDirectSumEsa.lean — theorem BookProof.DirectSumEsa.fockH_isSymmetricDom
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
import Definitions.Def_ChapterNavierStokesFullEsa
import Theorems.Thm_BookProof_NavierStokesFlow_FullEsa_IsSymmetricDom_sub
import Definitions.Def_ChapterAbelianGelfandModel
import Definitions.Def_ChapterBddBelowFiberSumEsa
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.NavierStokesFlow.FullEsa
open BookProof.NavierStokesFlow.FullEsa.NSFullData
open BookProof.DirectSumEsa


open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {D : ∀ i, Submodule ℂ (G i)}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

theorem BookProof.DirectSumEsa.fockH_isSymmetricDom {w : ℝ → ℝ} (hw : Measurable w) :
    IsSymmetricDom (fockH hw) := by sorry
