-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_original_finite_horizon_predictable_intensity_budget
-- name    : AvramDividend.Classical.avram_wave4_04_original_finite_horizon_predictable_intensity_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:41:51.350991+00:00
-- url     : https://prove2.me/theorems/6a25e164-a9aa-4694-b8e8-9a47ee895151
-- title:
--   Actual finite-horizon time-probability measure restricted to the controlled Lévy predictable space carries finite nonlinear jump L² energy
-- statement:
--   For the actual spectrally negative Lévy process X on (Ω,P), its original filtration, and the same adapted dividend strategy D, at each finite T construct μ on the right-continuous predictable sigma algebra. For every predictable event A, μ(A) is exactly the actual finite-horizon time-probability product measure of A. The time factor is the pushforward under Real.toNNReal of real Lebesgue measure restricted to [0,T], avoiding any incorrect assumption that NNReal has a default volume MeasureSpace instance. The source path X.isProbability ensures that P is finite. The controlled prepayment reserve and full negative-mark nonlinear jump kernel H are predictable-measurable and have finite nested L² integral against original X.ν and μ via the canonically Proved source-X,D kernel theorem. No first jump moment, copied Lévy law, compensator assumption, Brownian representation, arbitrary dividend Stieltjes Itô formula or corrected verification conclusion is asserted.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), same-original-process stochastic kernel L² observation measure. Source work/avram_wave4_04_finite_horizon_original_predictable_observation_probe.lean, SHA-256 64e9e51b9587c89688273029ea445758b2035502c32e6abe6f9d562c5cb24569. Pinned Mathlib predictable generator inclusion, finite real Lebesgue interval, map/product finite measure, trim event identity. Canonical Proved input 18dba881-66b9-4289-a702-c5538ebc5827. Revised private remote elaboration job eb90d1cc-6897-4982-bd51-b367b49ae35d pending, not a proof submission; published only after complete private diagnostic. Corrected primary 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_original_finite_horizon_predictable_intensity_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      (let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
         fun p => if Y p.1 ∈ Icc (u + δ) v then
           w (Y p.1 + p.2) - w (Y p.1) else 0
       Measurable[(𝓕.rightCont.predictable).prod
         (inferInstance : MeasurableSpace ℝ)] H ∧
       (∫⁻ p : ℝ≥0 × Ω,
         ∫⁻ z in Iio (0 : ℝ),
           ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤) := by sorry
