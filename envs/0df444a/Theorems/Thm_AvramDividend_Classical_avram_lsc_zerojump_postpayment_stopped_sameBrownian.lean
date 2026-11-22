-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_postpayment_stopped_sameBrownian
-- name    : AvramDividend.Classical.avram_lsc_zerojump_postpayment_stopped_sameBrownian
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T18:12:11.988362+00:00
-- url     : https://prove2.me/theorems/68bc4dba-badb-421b-9535-ae83ac29f82a
-- title:
--   One original Brownian driver for stopped controlled reserve, post-dividend terminal and filtration
-- statement:
--   Under original zero-Lévy-measure and unbounded-variation assumptions, for every admissible dividend strategy and original right-continuous stopping time, produce one Brownian motion on the original probability space with the transported real-time Brownian filtration and real-time stopping property. The same Brownian motion must give the reserve at every nonnegative time and the exact stopped post-payment terminal reserve (right dividend at strictly pre-ruin or zero clock, otherwise left reserve), while original controlled reserve paths are almost surely left-continuous. This combines the exact already proved separate interfaces into a single witness, needed for the source-faithful Ito–Stieltjes decomposition.
-- source:
--   Avram Dividend Classical mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43, root 545c65ef-edd3-4ecb-aeaa-8dd6c5bce0e7. Proved dependencies e72d0175-b6bd-45bf-ad30-0049fa7ed69a, 2580a61d-4f76-4c99-a088-ae28e8cf6e58, 37d963a0-712f-4f06-87d6-6a9238f0684c. Source exact right-dividend jump convention from fdb9a6a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_ubv_filtered_stopped_driver
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_controlled_reserve_brownian_leftCont
open MeasureTheory ProbabilityTheory Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_zerojump_postpayment_stopped_sameBrownian
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (Terminal : Ω → ℝ)
    (hTerminal : ∀ ω,
      Terminal ω =
        if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
        then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
        else riskProcess X x D (τ ω) ω) :
    ∃ (B : LevyStochCalc.Brownian.BrownianMotion P)
      (ℱr : Filtration ℝ mΩ),
      (∀ t : ℝ, ℱr t = 𝓕.rightCont (Real.toNNReal t)) ∧
      LevyStochCalc.Brownian.IsBrownianFiltration B ℱr ∧
      IsStoppingTime ℱr
        (fun ω => ((τ ω : ℝ) : WithTop ℝ)) ∧
      (∀ (t : ℝ≥0) (ω : Ω),
        riskProcess X x D t ω =
          x + (t : ℝ) * X.c + X.σ * B.W (t : ℝ) ω - D t ω) ∧
      (∀ ω,
        Terminal ω =
          if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + (τ ω : ℝ) * X.c + X.σ * B.W (τ ω : ℝ) ω -
            rightLimit D (τ ω) ω
          else x + (τ ω : ℝ) * X.c + X.σ * B.W (τ ω : ℝ) ω -
            D (τ ω) ω) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => riskProcess X x D u ω)
          (Set.Iic t) t) := by sorry
