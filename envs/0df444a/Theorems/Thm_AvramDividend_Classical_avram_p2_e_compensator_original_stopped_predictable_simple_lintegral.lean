-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_stopped_predictable_simple_lintegral
-- name    : AvramDividend.Classical.avram_p2_e_compensator_original_stopped_predictable_simple_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:12:31.101345+00:00
-- url     : https://prove2.me/theorems/c743961b-276e-4cba-a472-bb5a1ee0225b
-- title:
--   Actual original stopped predictable nonnegative simple-integrand Lebesgue compensation
-- statement:
--   The full nonnegative Lebesgue integral of an arbitrary finite simple predictable-rectangle integrand under the stopped actual source marked jump mean measure equals its integral under the genuine physical-clock negative Levy compensator, on the same original filtration and probability space. Each cell is a Borel-marked strict-future right-continuous past event, with explicit product predictable measurability and arbitrary nonnegative ENNReal coefficient. Finite sums and measurable indicator integrals preserve infinite-activity cases. Proof reduces through public Proved original stopped strict-future rectangle compensation 92775667 and exact pinned Mathlib indicator/finite-integral-sum lemmas; no replacement process, independence postulate or new axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p2_e_compensator_original_stopped_predictable_simple_lintegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω = ((Measure.count.restrict
      {u : ℝ≥0 | 0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω = @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
      (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))
      (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ E : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] E →
      μ E = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) E)
    (N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _
        (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ)))
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable;
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    {ι : Type*} (S : Finset ι)
    (i : ι → ℝ≥0) (A : ι → Set Ω)
    (hA : ∀ k ∈ S, MeasurableSet[𝓕.rightCont (i k)] (A k))
    (B : ι → Set ℝ) (hB : ∀ k ∈ S, MeasurableSet (B k))
    (E : ι → Set ((ℝ≥0 × Ω) × ℝ))
    (hE : ∀ k ∈ S, E k = (Ioi (i k) ×ˢ A k) ×ˢ B k)
    (hEm : ∀ k ∈ S, MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] (E k))
    (w : ι → ℝ≥0∞) :
    (∫⁻ p, ∑ k ∈ S, (E k).indicator (fun _ => w k) p
        ∂(M.restrict {p | p.1.1 ≤ T})) =
      ∫⁻ p, ∑ k ∈ S, (E k).indicator (fun _ => w k) p ∂N := by sorry
