-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_one_event_source_residual_and_controlled_reserve_variation
-- name    : AvramDividend.Classical.avram_wave5_04a_actual_bv_one_event_source_residual_and_controlled_reserve_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T13:21:16.489202+00:00
-- url     : https://prove2.me/theorems/7a8a03e6-1688-46d7-a566-c143528329dc
-- title:
--   One a.s. event: exact source residual BV decomposition, discounted HJB sign and true controlled-reserve finite variation
-- statement:
--   Under Standing and BoundedVariation for the actual spectrally negative Levy process and an actual dividend strategy, almost surely one source residual R is explicitly defined from drift, source position and all intrinsic negative original left jumps; it is monotone, gives exact source intervals, exact partition variation and a nonpositive discounted local HJB contribution. Simultaneously on that same sample event, the actual controlled reserve riskProcess has the previously Proved finite-partition variation bound involving source drift, source position and chronological dividend D increments. This is an interface for Chat03 controlled C1 integration without assuming the controlled Ito-Meyer identity.
-- source:
--   Chat04-A one-event source/control BV bridge; combines canonically Proved positive-cap one-R source interface aa45c108-4acc-4b90-ba95-6a8b16298408 with original controlled reserve variation 2faae607-6a38-40ab-a87f-de5c4dbf9672.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_positive_cap_one_remainder_exact_decomposition_variation_discounted_sign
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_reserve_partition_variation

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- One samplewise event supports both the exact source BV remainder and
the actual controlled reserve's finite-partition variation, while keeping
source left jumps separate from chronological right dividend payments. -/

theorem AvramDividend.Classical.avram_wave5_04a_actual_bv_one_event_source_residual_and_controlled_reserve_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) :
    ∀ᵐ ω ∂P, ∃ R : ℝ≥0 → ℝ,
      (∀ t : ℝ≥0,
        R t = ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (v : ℝ≥0),
            if 0 < v ∧ v ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
            else 0).toReal) ∧
      Monotone R ∧
      (∀ (s t : ℝ≥0) (hst : s ≤ t),
        X.X t ω - X.X s ω =
          ((t : ℝ) - (s : ℝ)) * X.drift -
            (∑' (v : ℝ≥0),
              if s < v ∧ v ≤ t then
                ENNReal.ofReal (Function.leftLim
                  (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
              else 0).toReal -
            (R t - R s)) ∧
      (∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (Finset.range n).sum (fun i =>
          |R (u (i + 1)) - R (u i)|) =
        R (u n) - R (u 0)) ∧
      (∀ (τ : Ω → ℝ≥0) (u : ℕ → ℝ≥0)
        (hu : Monotone u) (n : ℕ) (hstop : u n ≤ τ ω)
        (hinterior : ∀ i : Fin n,
          0 < riskProcess X x D (u i) ω ∧
            ENNReal.ofReal (riskProcess X x D (u i) ω) < C),
        (∑ i : Fin n,
          -(Real.exp (-(q * (u i : ℝ))) *
            deriv w (riskProcess X x D (u i) ω)) *
              (R (u (i + 1)) - R (u i))) ≤ 0) ∧
      (∀ (u : ℕ → ℝ≥0) (hu : Monotone u) (n : ℕ),
        (∑ i ∈ Finset.range n,
          |riskProcess X x D (u (i + 1)) ω -
            riskProcess X x D (u i) ω|) ≤
          2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
            (X.X (u n) ω - X.X (u 0) ω) +
            (D (u n) ω - D (u 0) ω)) := by sorry
