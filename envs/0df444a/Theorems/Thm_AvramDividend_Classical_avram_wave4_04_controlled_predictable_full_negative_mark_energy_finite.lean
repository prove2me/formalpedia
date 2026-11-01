-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
-- name    : AvramDividend.Classical.avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T19:23:13.937202+00:00
-- url     : https://prove2.me/theorems/18dba881-66b9-4289-a702-c5538ebc5827
-- title:
--   Actual controlled Lévy source predictable negative-jump kernel has finite time-space quadratic energy on compact interior reserve bands
-- statement:
--   For the same original spectrally negative Lévy path X and an arbitrary dividend strategy D adapted to its filtration, the pre-payment reserve is strongly predictable in the right-continuous predictable sigma algebra. If the pre-payment reserve lies in a fixed compact interior band [u+δ,v], the full nonlinear jump amplitude H(t,ω,z)=w(Y(t,ω)+z)-w(Y(t,ω)), zero outside that band, is measurable on the predictable space times the mark space. Under the original source Lévy measure ν, its squared amplitude is integrable over negative marks and then over any finite observation measure μ on that same predictable sigma algebra, with an explicit constant bound independent of t, ω, z and μ. The payoff w is only assumed continuous on nonnegative reserves and zero below ruin; its global measurability is derived, not assumed. All negative marks including jumps across ruin are included. The proof uses ν's square-integrability and no finite first absolute jump moment. This is an analytic predictable L² admissibility step. It does not establish that the actual X jump count has compensator dt ν(dz), construct the compensated integral or Brownian martingale, handle singular dividend Stieltjes mass or cap local time, or assert the corrected full verification inequality.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), controlled original-process jump integrand. Pinned source is 7,199 bytes SHA-256 1b1c520dc3a0f1a1fb9a0fbe404e5412ec4ba413d7b96a705557405c91cecbc6 at work/avram_wave4_04_controlled_predictable_mark_energy_probe.lean. Dependencies: proved uniform original-source ν quadratic envelope UUID 00ebb997-58eb-47ba-9a38-1e3bf9937d4f and proved actual X,D prepayment reserve strong predictability UUID 94ee9994-3882-4f29-8637-06666efe721d. Private remote probe job 256f2027-05eb-42d1-84c2-0970f617196e submitted against pinned revision, its terminal diagnostics must be checked. Corrected primary prerequisite UUID 429e17ca-5528-40b5-b593-7c03973d0706.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_full_negative_mark_uniform_quadratic_envelope

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry
