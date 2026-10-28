-- Prove2me | Theorems.Thm_AvramDividend_Classical_submartingale_ae_zero_of_l1_bound_and_convergence_in_measure_ws01b
-- name    : AvramDividend.Classical.submartingale_ae_zero_of_l1_bound_and_convergence_in_measure_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:42:47.710948+00:00
-- url     : https://prove2.me/theorems/bef98e41-23e8-4592-9e51-935e000033b4
-- title:
--   Bounded submartingale converging in measure to zero converges almost surely to zero
-- statement:
--   A real-valued submartingale with uniformly bounded L1 norms and almost-everywhere measurable terms converges pointwise almost surely to zero whenever it converges in measure to zero. Apply Doob almost-sure convergence, convergence in measure of the almost-sure limit, and uniqueness of limits in measure. This identifies the zero small-time limit in the backwards-martingale proof for bounded-variation Lévy drift deficits.
-- source:
--   Bertoin, Subordinators (backwards-martingale small-time slope method); pinned Mathlib theorems MeasureTheory.Submartingale.ae_tendsto_limitProcess, MeasureTheory.tendstoInMeasure_of_tendsto_ae, MeasureTheory.tendstoInMeasure_ae_unique. Primary BV lower no-creeping obligation 43a28d8e under stopped-scale primary 09caed2c.

import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Tactic

open MeasureTheory Filter Topology

theorem AvramDividend.Classical.submartingale_ae_zero_of_l1_bound_and_convergence_in_measure_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓖 : Filtration ℕ mΩ}
    (f : ℕ → Ω → ℝ) (R : NNReal)
    (hSub : Submartingale f 𝓖 P)
    (hBound : ∀ n : ℕ, eLpNorm (f n) (1 : ENNReal) P ≤ ENNReal.ofNNReal R)
    (hMeas : ∀ n : ℕ, AEStronglyMeasurable (f n) P)
    (hMeasure : TendstoInMeasure P f atTop (fun _ : Ω => (0 : ℝ))) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 (0 : ℝ)) := by sorry
