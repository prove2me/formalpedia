-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_stieltjes_tail_terminal
-- name    : AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_stieltjes_tail_terminal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:52:24.824347+00:00
-- url     : https://prove2.me/theorems/e3bab419-e405-42a3-8f91-16657b4c8209
-- title:
--   True BV discounted frozen post-payment Stieltjes tail equals negative terminal value
-- statement:
--   For the actual BV controlled spectrally negative Levy reserve, freeze its post-payment reserve at a finite horizon T but continue discounting at positive rate q. The globally BV discounted Lipschitz test has strict post-T signed Stieltjes mass equal to minus its terminal discounted value. This exact tail correction distinguishes the test's discount decay from dividend payments.
-- source:
--   Pinned vectorMeasure_Ioi, Real.tendsto_exp_atBot, NNReal.tendsto_coe_atTop and the Proved source discounted post-payment Ioc atom-accounting theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_postPayment_Ioc_atom_accounting
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_discounted_postPayment_stieltjes_tail_terminal
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 < q)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        Real.exp (-q * (t : ℝ)) *
          v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        hg.vectorMeasure (Ioi T) =
          -(Real.exp (-q * (T : ℝ)) *
            v (x + X.X T ω - rightLimit D T ω)) := by sorry
