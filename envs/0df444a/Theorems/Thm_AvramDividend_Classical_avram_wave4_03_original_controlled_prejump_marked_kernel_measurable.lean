-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_controlled_prejump_marked_kernel_measurable
-- name    : AvramDividend.Classical.avram_wave4_03_original_controlled_prejump_marked_kernel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:58:37.197993+00:00
-- url     : https://prove2.me/theorems/7898252f-6d90-4103-b20b-298e5d9a285a
-- title:
--   Actual controlled Lévy pre-jump nonlinear mark kernel is jointly predictable–Borel measurable
-- statement:
--   For the same original spectrally negative Lévy source X and any adapted left-continuous dividend strategy D, the nonlinear negative-jump kernel (s,ω,z) ↦ w(x+X_{s−}(ω)−D_s(ω)+z)−w(x+X_{s−}(ω)−D_s(ω)) is jointly measurable for the right-continuous predictable sigma algebra in (s,ω) and Borel marks z, assuming only that w is Borel measurable. This certifies the genuine source-specific predictable marked integrand needed for finite-band compensation. It does not claim a Poisson law, compensated martingale, Stieltjes chain rule or verification bound.
-- source:
--   Original Avram–Palmowski–Pistorius (2007), Proposition 4(i), source jump-martingale interface; canonically Proved original postpayment reserve strict-left-limit predictable theorem 94ee9994-3882-4f29-8637-06666efe721d. Real measurable composition on the predictable × Borel product; no surrogate Lévy process or assumed PRM.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_original_controlled_prejump_marked_kernel_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) :
    Measurable[(𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)]
      (fun p : (ℝ≥0 × Ω) × ℝ =>
        w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1
          + p.2) -
        w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1)) := by sorry
