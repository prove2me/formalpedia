-- Prove2me | Theorems.Thm_BookProof_OperatorSeries_seriesOp_commForm_le
-- name    : BookProof.OperatorSeries.seriesOp_commForm_le
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-05T21:29:59.034572+00:00
-- url     : https://prove2.me/theorems/d4959088-0c1a-4521-bf28-8c1cce3b3381
-- title:
--   `BookProof.OperatorSeries.seriesOp_commForm_le` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) {b : κ → ℝ} (hb : Summable b
-- statement:
--   Prove the following Lean 4 theorem from `ChapterOperatorSeriesEsa`.
--
--   `BookProof.OperatorSeries.seriesOp_commForm_le` (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖) (ha : Summable a) {b : κ → ℝ} (hb : Summable b) (hcomm : ∀ (k : κ) (x : maxDom c), |commForm (T k) (diagMax c) x| ≤ b k * quadForm (diagMax c) x) (hq : ∀ x : maxDom c, 0 ≤ quadForm (diagMax c) x) (x : maxDom c) : |commForm (seriesOp T a hnorm ha) (diagMax c) x| ≤ (∑' k, b k) * quadForm (diagMax c) x
--
--   Formalization note: Lean 4 identifier `BookProof.OperatorSeries.seriesOp_commForm_le`.

-- Generated from ChapterOperatorSeriesEsa.lean — theorem BookProof.OperatorSeries.seriesOp_commForm_le
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

theorem BookProof.OperatorSeries.seriesOp_commForm_le
    (hnorm : ∀ (k : κ) (x : maxDom c), ‖(T k x : L2I ι)‖ ≤ a k * ‖(diagMax c x : L2I ι)‖)
    (ha : Summable a) {b : κ → ℝ} (hb : Summable b)
    (hcomm : ∀ (k : κ) (x : maxDom c),
      |commForm (T k) (diagMax c) x| ≤ b k * quadForm (diagMax c) x)
    (hq : ∀ x : maxDom c, 0 ≤ quadForm (diagMax c) x) (x : maxDom c) :
    |commForm (seriesOp T a hnorm ha) (diagMax c) x| ≤ (∑' k, b k) * quadForm (diagMax c) x := by sorry
