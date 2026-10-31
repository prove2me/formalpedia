-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
-- name    : AvramDividend.Classical.avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T22:03:49.340517+00:00
-- url     : https://prove2.me/theorems/b65b82f2-497b-40cf-8137-1325f2886f7f
-- title:
--   Complete corrected UBV stochastic verification at cap zero for arbitrary admissible initial capital and finite horizon
-- statement:
--   For every original unbounded-variation spectrally negative Lévy process, every admissible original adapted left-continuous dividend strategy with cap C=0 and arbitrary real initial reserve x satisfying ENNReal.ofReal(x)≤0, any real discount rate q and nonnegative finite real horizon T, the entire exact expected discounted original Stieltjes dividend reward on all payment times through T is bounded by the verification candidate w(x), provided only the corrected boundary premise w(0)≥0. The actual admissibility and cap premises force x=0 using initial payment solvency and monotone dividends; the already verified unbounded-variation zero-cap all-horizon stochastic lemma then gives zero exact Stieltjes reward. This is the complete C=0 branch of the corrected UBV source-process stochastic verification theorem, even without assuming generator/HJB regularity, thereby isolating the remaining nonzero-cap continuous-time Itô–Meyer problem.
-- source:
--   Pinned private remote candidate-probe 22c8adc3-067c-4260-902d-c05437aab606 passed its intentional sentinel without source errors, SHA256 10215366631c7a1db33544b1dca32383eeeba73eae58da41ce957e0104a85ffe. Canonical Proved zeroCap_admissibleInitialCapital_eq_zero d781e680-4dde-40c1-b6dc-f415a203b56e and ubv_zeroCap_allHorizon_stieltjesReward_zero 771fa12d-84c9-4f86-82bb-6245490a8831; pinned Mathlib Real.coe_toNNReal.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_zeroCap_admissibleInitialCapital_eq_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_zeroCap_allHorizon_stieltjesReward_zero

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_04_corrected_ubv_zeroCap_fullHorizon_allInitialCapital
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ (0 : ℝ≥0∞))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x 0 D)
    (q : ℝ) (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by sorry
