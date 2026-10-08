-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_essentiallySelfAdjointOn_finiteModes_of_bounds
-- name    : BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T21:30:49.912288+00:00
-- url     : https://prove2.me/theorems/45a9d048-324f-426e-97d7-45cc26487632
-- title:
--   `BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds` (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H : maxDom c →ₗ[ℂ] L2I ι) (A B : ℝ) (hB : 0 ≤ B) (hsym : SymmetricOn (max
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds` (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (H : maxDom c →ₗ[ℂ] L2I ι) (A B : ℝ) (hB : 0 ≤ B) (hsym : SymmetricOn (maxDom c) H) (hA : ∀ x : maxDom c, ‖(H x : L2I ι)‖ ≤ A * ‖(diagMax c x : L2I ι)‖) (hcomm : ∀ x : maxDom c, |commForm H (diagMax c) x| ≤ B * quadForm (diagMax c) x) : EssentiallySelfAdjointOn (lpFiniteModes ι) (H.comp (Submodule.inclusion (finiteModes_le_maxDom c)))
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterNavierStokesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.OperatorSeries

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι κ : Type*} {c : ι → ℝ}
variable (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a : κ → ℝ)
variable {T} {a}
variable {ι : Type*} {c : ι → ℝ}



open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

theorem BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_bounds (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k)
    (H : maxDom c →ₗ[ℂ] L2I ι) (A B : ℝ) (hB : 0 ≤ B) (hsym : SymmetricOn (maxDom c) H)
    (hA : ∀ x : maxDom c, ‖(H x : L2I ι)‖ ≤ A * ‖(diagMax c x : L2I ι)‖)
    (hcomm : ∀ x : maxDom c, |commForm H (diagMax c) x| ≤ B * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      (H.comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by sorry
