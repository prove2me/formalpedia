-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_seriesOp_apply
-- name    : BookProof.OperatorSeries.seriesOp_apply
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:21:24.429121+00:00
-- url     : https://prove2.me/theorems/1d1fb0c2-8ea3-4202-a591-4357d619a61c
-- title:
--   `BookProof.OperatorSeries.seriesOp_apply` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (x : maxDom c) : (seriesOp T a hno
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.seriesOp_apply` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (x : maxDom c) : (seriesOp T a hnorm ha x : L2I ι) = ∑' k, (T k x : L2I ι)
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.seriesOp_apply`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.seriesOp_apply
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

theorem BookProof.OperatorSeries.seriesOp_apply
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (x : maxDom c) :
    (seriesOp T a hnorm ha x : L2I ι) = ∑' k, (T k x : L2I ι) := by sorry
