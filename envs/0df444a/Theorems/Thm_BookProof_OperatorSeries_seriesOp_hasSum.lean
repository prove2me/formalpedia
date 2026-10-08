-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_seriesOp_hasSum
-- name    : BookProof.OperatorSeries.seriesOp_hasSum
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:22:31.034003+00:00
-- url     : https://prove2.me/theorems/983a6b75-2b90-42a8-9785-c65ce5f5a6c2
-- title:
--   `BookProof.OperatorSeries.seriesOp_hasSum` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (x : maxDom c) : HasSum (fun k =>
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.seriesOp_hasSum` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (x : maxDom c) : HasSum (fun k => (T k x : L2I ι)) (seriesOp T a hnorm ha x)
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.seriesOp_hasSum`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.seriesOp_hasSum
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

theorem BookProof.OperatorSeries.seriesOp_hasSum
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (x : maxDom c) :
    HasSum (fun k => (T k x : L2I ι)) (seriesOp T a hnorm ha x) := by sorry
