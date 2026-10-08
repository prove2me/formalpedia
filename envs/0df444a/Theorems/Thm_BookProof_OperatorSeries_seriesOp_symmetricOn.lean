-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_seriesOp_symmetricOn
-- name    : BookProof.OperatorSeries.seriesOp_symmetricOn
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:22:39.965737+00:00
-- url     : https://prove2.me/theorems/a82cac3a-297f-410f-802e-57c705d48f52
-- title:
--   `BookProof.OperatorSeries.seriesOp_symmetricOn` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (hsym : ∀ k, SymmetricOn (ma
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.seriesOp_symmetricOn` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) (hsym : ∀ k, SymmetricOn (maxDom c) (T k)) : SymmetricOn (maxDom c) (seriesOp T a hnorm ha)
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.seriesOp_symmetricOn`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.seriesOp_symmetricOn
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Mathlib
import Definitions.Def_ChapterOperatorSeriesEsa
import Definitions.Def_ChapterFarisLavineCore
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

theorem BookProof.OperatorSeries.seriesOp_symmetricOn
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) (hsym : ∀ k, SymmetricOn (maxDom c) (T k)) :
    SymmetricOn (maxDom c) (seriesOp T a hnorm ha) := by sorry
