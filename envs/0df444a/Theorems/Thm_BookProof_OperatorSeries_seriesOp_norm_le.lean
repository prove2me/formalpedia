-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_seriesOp_norm_le
-- name    : BookProof.OperatorSeries.seriesOp_norm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:29:25.284573+00:00
-- url     : https://prove2.me/theorems/58f57dd4-cd5b-429d-8def-bc9c4b23e7c1
-- title:
--   `BookProof.OperatorSeries.seriesOp_norm_le` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (x : maxDom c) : ‖(seriesOp T a
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.seriesOp_norm_le` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (x : maxDom c) : ‖(seriesOp T a hnorm ha x : L2I ι)‖ ≤ (∑' k, a k) * ‖(diagMax c x : L2I ι)‖
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.seriesOp_norm_le`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.seriesOp_norm_le
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterNavierStokesIkebeKato
open BookProof.NavierStokesFlow.IkebeKato
open BookProof.OperatorSeries

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {ι κ : Type*} {c : ι → ℝ}
variable (T : κ → (maxDom c →ₗ[ℂ] L2I ι)) (a : κ → ℝ)
variable {T} {a}



open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat

noncomputable section

theorem BookProof.OperatorSeries.seriesOp_norm_le
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (x : maxDom c) :
    ‖(seriesOp T a hnorm ha x : L2I ι)‖ ≤ (∑' k, a k) * ‖(diagMax c x : L2I ι)‖ := by sorry
