-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_exponential_strictKilled_dyadic_rightMesh_tendsto
-- name    : AvramDividend.Classical.avram_wave4_03_source_postPayment_exponential_strictKilled_dyadic_rightMesh_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:51:33.995445+00:00
-- url     : https://prove2.me/theorems/dd7f2796-39a8-4b46-98ee-516c161ed777
-- title:
--   Genuine original source Lévy discounted postpayment integrand converges under strict ruin killing
-- statement:
--   For actual original X and same D, exact right dyadic sampled exponential postpayment controlled wealth with strict killing at arbitrary extended-real τ converges at every time s≤T, including s=τ where right endpoints exclude the ruin atom. The proof combines accepted original path right dyadic convergence, right-endpoint monotonicity, continuity ℝ≥0→ENNReal and an eventually-correct strict killing indicator. Supports full positive-horizon stopped Stieltjes Fatou without a fictional PRM or atomic-only approximation.
-- source:
--   Accepted source postPayment exponential dyadic right-mesh 608b8b12 and accepted source dyadic endpoint limit da8556b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_exponential_dyadic_rightMesh_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_scaled_dyadic_ceiling_horizon_limit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_wave4_03_source_postPayment_exponential_strictKilled_dyadic_rightMesh_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (θ q : ℝ) (ω : Ω) (s T : ℝ≥0)
    (hT : 0 < T) (hs : s ≤ T) (τ : ℝ≥0∞) :
    Tendsto
      (fun n : ℕ =>
        let k := Nat.ceil (((s / T : ℝ≥0) : ℝ) * (2 : ℝ) ^ n)
        let u := ((k : ℝ≥0) / (2 : ℝ≥0) ^ n) * T
        if (u : ℝ≥0∞) < τ then
          Real.exp (θ * (x + X.X u ω - rightLimit D u ω) -
            (u : ℝ) * q) else 0) atTop
      (𝓝 (if (s : ℝ≥0∞) < τ then
        Real.exp (θ * (x + X.X s ω - rightLimit D s ω) -
          (s : ℝ) * q) else 0)) := by sorry
