-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_intrinsic_stopped_mark_band_l2_limit_mean_zero
-- name    : AvramDividend.Classical.avram_wave5_p1_original_intrinsic_stopped_mark_band_l2_limit_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:37:42.427068+00:00
-- url     : https://prove2.me/theorems/378b0a4c-5b0a-412b-b3c6-840ee1551899
-- title:
--   Original Lévy stopped finite-mark-band compensated jumps admit a centred L² limit under explicit source Fubini and quadratic-tail bounds
-- statement:
--   For the unchanged actual original SpectrallyNegativeLevy path and filtration, each band reward is the literal integral against its intrinsic pathwise marked-jump measure up to an original stopping time, less the predictable compensator integral. The original source expected marked occupation and Lévy intensity agree on adapted predictable rectangles under finite-band localisation, and source Fubini is explicitly required. These facts centre each source band. If the source variables have L² representatives satisfying a genuine source-coupled quadratic-tail distance estimate with finite-rate marks, their L²(P) limit exists and has expectation zero. This is conditional on the actual intrinsic-jump isometry estimate, which is not derived from an unrelated Poisson copy.
-- source:
--   Compose Proved actual-source signed stopped compensation f544dab9-21ae-4ce6-b2a1-1c4041802831 with Proved actual-probability L² band limit 540bd939-b21d-4883-901a-fc40fbf58ec6. Distinct from clipped-source-increment limit 9edde1b5 and addressed to Chat 03-B actual intrinsic marked jump compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_actual_source_stopped_signed_jump_compensation_of_rectangles
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_actual_probability_l2_stopped_band_limit_mean_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_p1_original_intrinsic_stopped_mark_band_l2_limit_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))))
    (M N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (B : ℕ → Set ℝ) (hBm : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = Set.univ)
    (hLocal : ∀ n, M ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B n) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 ⊥] A → MeasurableSet C →
      M (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C) =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C : Set ℝ),
      MeasurableSet[𝓕 i] A → MeasurableSet C →
      M ((Set.Ioi i ×ˢ A) ×ˢ C) =
        N ((Set.Ioi i ×ˢ A) ×ˢ C))
    (ν : Measure ℝ) (hBfinite : ∀ n, ν (B n) < ∞)
    (f : ℝ → ℝ) (hf : Measurable f)
    (henergy : ∫⁻ z, ‖f z‖ₑ ^ (2 : ℝ) ∂ν < ∞)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (G : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (Gband : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hGband : ∀ n,
      Gband n = ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B n).indicator G)
    (hGm : ∀ n, Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.predictable) (inferInstance : MeasurableSpace ℝ))] (Gband n))
    (hGi : ∀ n, Integrable (Gband n) M)
    (H : ℕ → ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hH : ∀ n, H n = fun p =>
      if (p.1.1 : ℝ≥0∞) ≤ τ p.1.2 then Gband n p else 0)
    (hActualI : ∀ n, Integrable
      (fun ω => ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) P)
    (hSourceFubini : ∀ n,
      (∫ ω, ∫ p, H n ((p.1, ω), p.2) ∂(NX ω) ∂P) =
        ∫ p, H n p ∂M)
    (V : ℕ → Ω → ℝ)
    (hV : ∀ n, V n = fun ω =>
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
        ∫ p, H n p ∂N)
    (L : ℕ → Lp ℝ (2 : ℝ≥0∞) P)
    (hRep : ∀ n, (L n : Ω → ℝ) =ᵐ[P] V n)
    (hbound : ∀ m n, m ≤ n →
      dist (L m) (L n) ≤
        (eLpNorm ((B m)ᶜ.indicator f) (2 : ℝ≥0∞) ν).toReal) :
    ∃ Llimit : Lp ℝ (2 : ℝ≥0∞) P,
      Tendsto L Filter.atTop (nhds Llimit) ∧
        (∫ ω, Llimit ω ∂P) = 0 := by sorry
