-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_controlled_reserve_brownian_leftCont
-- name    : AvramDividend.Classical.avram_lsc_zerojump_original_controlled_reserve_brownian_leftCont
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T17:53:41.407365+00:00
-- url     : https://prove2.me/theorems/2580a61d-4f76-4c99-a088-ae28e8cf6e58
-- title:
--   Controlled original zero-jump reserve: exact Brownian-minus-dividend path and almost-sure left-continuity
-- statement:
--   For an original Avram zero-jump unbounded-variation Lévy source and arbitrary admissible dividend strategy, construct a same-original-space LevyStochCalc Brownian motion such that at every nonnegative time and every outcome the controlled risk reserve equals initial capital plus the deterministic source drift plus volatility times the Brownian path minus cumulative dividends. Moreover, the controlled risk process is left-continuous at every nonnegative time for almost every outcome, using the source path continuity and the dividend strategy's left-continuity. This identifies the exact controlled semimartingale structure and left-side reserve convention needed before deriving the dividend jump/Stieltjes terms in stopped Itô–Meyer. The declared probability typeclass instance is supplied by the original SpectrallyNegativeLevy.isProbability field at every use.
-- source:
--   Direct continuation of Avram source fdb9a6a3 and Gaussian branch 683607b6, 4aaca024. Verified canonical premises: 05b01179 original Brownian witness, 37d963a0 zero-jump sigma positivity, b462a147 zero-jump source a.s. continuity; IsAdmissibleLe includes IsDividendStrategy left-continuity. Source-facing application may synthesize the explicitly named IsProbabilityMeasure P from X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top11_original_zero_nu_global_continuous_ae
open MeasureTheory ProbabilityTheory Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_zerojump_original_controlled_reserve_brownian_leftCont
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      (∀ (t : ℝ≥0) (ω : Ω),
        riskProcess X x D t ω =
          x + (t : ℝ) * X.c + X.σ * W.W (t : ℝ) ω - D t ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => riskProcess X x D u ω)
          (Set.Iic t) t) := by sorry
