-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p3_vcstar_hjb_at_positive_cap_without_above_control
-- name    : AvramDividend.Classical.avram_wave4_p3_vcstar_hjb_at_positive_cap_without_above_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T16:13:00.790906+00:00
-- url     : https://prove2.me/theorems/9fc9114f-15eb-4b32-90cf-9fef3e177eed
-- title:
--   Positive optimal-barrier HJB equality and true generator domain without upper-region control
-- statement:
--   At a finite positive optimal barrier for a true q-scale function of the original spectrally negative Levy process under Standing, the classical candidate belongs to the actual compensated generator domain and max((Gamma-q)vcstar,1-vcstar') vanishes at the barrier, under exactly the original three-way regularity alternative and no hypothesis about the generator above cstar. Import the Proved P3 stronger endpoint cap equality 0458283a (itself derived independently of original 918) and Proved exact derivative smooth fit edf21020, then evaluate max(0,0). This sharpens the original canonical positive-cap HJB 8d03da6b by dropping hgen, without touching Chat05's interior HJB or Chat06's stochastic verification.
-- source:
--   Avram, Palmowski, Pistorius (2007), Section 5 Lemma 4, HJB (5.8), smooth fit; P3 genuine cap equality 0458283a; derivative eq one edf21020.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_p3_vcstar_hjb_at_positive_cap_without_above_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    X.GeneratorIntegrable (vcstar W) (cstar W).toReal ∧
      max (X.generator (vcstar W) (cstar W).toReal -
        q * vcstar W (cstar W).toReal)
        (1 - deriv (vcstar W) (cstar W).toReal) = 0 := by sorry
