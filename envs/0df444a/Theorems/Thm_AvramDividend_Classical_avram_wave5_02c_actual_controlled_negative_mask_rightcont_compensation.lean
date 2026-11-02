-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_actual_controlled_negative_mask_rightcont_compensation
-- name    : AvramDividend.Classical.avram_wave5_02c_actual_controlled_negative_mask_rightcont_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:08:11.818348+00:00
-- url     : https://prove2.me/theorems/5a8ca76d-f1e3-4d25-bb92-5699adfc297c
-- title:
--   Actual original finite-horizon ruin-stopped controlled Taylor negative-mark masked jump compensation
-- statement:
--   For the same literal original spectrally negative Levy source and right-continuous dividend control, the kernel is explicitly masked to the original negative jump marks z<0, the deterministic horizon t≤T, and the inclusive ruin-stop t≤τ. With precisely the source-kernel measurability and adapted-rectangle assumptions retained, the actual source jump integral is L1, its predictable compensation is the genuine restricted negative Levy intensity, and the expected discrepancy vanishes exactly. The ruin-causing jump remains included.
-- source:
--   Explicit negative-mark masked refinement of proved 02-C source right-continuous compensation and Chat03 ruin-stopped C² Taylor energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_ruinTime_rightCont_stopping_time
import Theorems.Thm_AvramDividend_Classical_avram_wave5_p1_original_rightcont_intrinsic_horizon_stopped_compensation_from_restricted_l1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_02c_actual_controlled_negative_mask_rightcont_compensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (NX : Ω → Measure (ℝ≥0 × ℝ))
    (hNX : ∀ ω, NX ω =
      ((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t))))
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2)) (NX ω))
    (hKmeas : AEMeasurable K P)
    (M : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hM : M = P.bind K)
    (T : ℝ≥0) (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hST : S = {p | p.1.1 ≤ T})
    (hS : MeasurableSet[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] S)
    (MT N : @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ (𝓕.rightCont.predictable)
        (inferInstance : MeasurableSpace ℝ)))
    (hMT : MT = M.restrict S)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hN : N = (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      μ.prod (X.ν.restrict (Iio (0 : ℝ)))))
    (B : ℕ → Set ℝ) (hBm : ∀ k, MeasurableSet (B k))
    (hBmono : Monotone B) (hBcover : (⋃ k, B k) = Set.univ)
    (hLocal : ∀ k, MT ((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ B k) ≠ ∞)
    (hBot : ∀ (A : Set Ω) (C' : Set ℝ),
      MeasurableSet[𝓕.rightCont ⊥] A → MeasurableSet C' →
      MT (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C') =
        N (({(⊥ : ℝ≥0)} ×ˢ A) ×ˢ C'))
    (hFuture : ∀ (i : ℝ≥0) (A : Set Ω) (C' : Set ℝ),
      MeasurableSet[𝓕.rightCont i] A → MeasurableSet C' →
      MT ((Set.Ioi i ×ˢ A) ×ˢ C') =
        N ((Set.Ioi i ×ˢ A) ×ˢ C')) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t p.2 - rightLimit D t p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * J p
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      S.indicator (((Set.univ : Set (ℝ≥0 × Ω)) ×ˢ Iio (0 : ℝ)).indicator HS)
    Measurable[(@Prod.instMeasurableSpace _ _
      (𝓕.rightCont.predictable) (inferInstance : MeasurableSpace ℝ))] G ∧
    Integrable G MT ∧ Integrable G N ∧
    Integrable (fun ω => ∫ p, G ((p.1, ω), p.2) ∂NX ω) P ∧
    (∫ ω, ∫ p, G ((p.1, ω), p.2) ∂NX ω ∂P) - (∫ p, G p ∂N) = 0 := by sorry
