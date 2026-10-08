-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_essentiallySelfAdjointOn_finiteModes_of_series
-- name    : BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-05T21:31:46.194987+00:00
-- url     : https://prove2.me/theorems/df747d8a-5d2a-445b-8c5b-323ad71becf4
-- title:
--   `BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series` {κ : Type*} (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a b : κ → ℝ)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series` {κ : Type*} (c : ι → ℝ) (hc : ∀ k, 0 ≤ c k) (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a b : κ → ℝ) (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) (hsym : ∀ k, SymmetricOn (maxDom c) (T k)) (hcomm : ∀ (k : κ) (x : maxDom c), |commForm (T k) (diagMax c) x| ≤ b k * quadForm (diagMax c) x) : EssentiallySelfAdjointOn (lpFiniteModes ι) ((seriesOp T a hnorm ha).comp (Submodule.inclusion (finiteModes_le_maxDom c)))
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series
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

theorem BookProof.OperatorSeries.essentiallySelfAdjointOn_finiteModes_of_series {κ : Type*} (c : ι → ℝ)
    (hc : ∀ k, 0 ≤ c k) (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a b : κ → ℝ)
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k)
    (hsym : ∀ k, SymmetricOn (maxDom c) (T k))
    (hcomm : ∀ (k : κ) (x : maxDom c),
      |commForm (T k) (diagMax c) x| ≤ b k * quadForm (diagMax c) x) :
    EssentiallySelfAdjointOn (lpFiniteModes ι)
      ((seriesOp T a hnorm ha).comp (Submodule.inclusion (finiteModes_le_maxDom c))) := by sorry
