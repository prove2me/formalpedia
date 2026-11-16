-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_original_uniform_ae_contact_budget_counterexample
-- name    : AvramDividend.Classical.avram_bvb_original_uniform_ae_contact_budget_counterexample
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T10:03:40.906666+00:00
-- url     : https://prove2.me/theorems/3af5da11-e4c1-47e5-8bd8-360fa7c57070
-- title:
--   Concrete original Standing BV positive-cap source disproves a.e. vanishing drift-only zero-contact physical cash excess
-- statement:
--   Construct an actual original Standing BV finite-activity negative-uniform Lévy source with a positive-probability jump-free unit-linear path. At finite cap 1 and horizon 1/10, the original zero-barrier Stieltjes stopped physical-grid cash plus terminal half-affine reward strictly exceeds the initial candidate while the masked drift-only physical grid is zero on that event. Thus the precise stopped positive-part physical excess, including the zero-ruin branch, does not converge to zero a.e. This challenges the zero-reserve contact survivor leaf of the original BV mission.
-- source:
--   Combine Proved exact original law with positive nojump event, the proposed original physical cash and drift ledger pointwise nonconvergence theorem, Proved original survival past 1/10 and the positive-probability a.e. refutation lemma. No alternate risk/dividend/stopping clocks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bvb_original_uniform_ae_contact_budget_counterexample :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 ∧
      0 < P {ω |
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 (1 : ℝ≥0) ×ˢ Iio (0 : ℝ)) = 0 ∧
        (∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) → X.X t ω = (t : ℝ) * X.drift)} ∧
      (let D := barrierStrategy X 0 0
       let T : ℝ := 1 / 10
       let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
       let u : ℕ → ℕ → ℝ≥0 := fun n i =>
         ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
       let F : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
             Iio (T - T / ((n : ℝ) + 2)),
           ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
           (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
             Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
            else 0)
       let L : ℕ → ((ℕ → ℝ) × (ℕ → ℝ)) → ℝ := fun n ω =>
         let Z : ℕ → ℝ := fun i => Function.leftLim
           (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
         ∑ i ∈ Finset.range (n + 1),
           if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
             Real.exp (-(u n i : ℝ)) *
               (X.drift * deriv w (Z i) - w (Z i)) *
               ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0

       ¬ (∀ᵐ ω ∂P,
         Tendsto (fun n => if ruinTime X 0 D ω = 0 then 0
           else max (F n ω - (w 0 + L n ω)) 0)
           atTop (𝓝 (0 : ℝ)))) := by sorry
