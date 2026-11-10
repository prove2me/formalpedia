-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_summable_annulus_centered_L2_limit
-- name    : AvramDividend.Classical.avram_mix_inf20_original_summable_annulus_centered_L2_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T18:45:02.166136+00:00
-- url     : https://prove2.me/theorems/b1173b50-8a5e-470d-9708-bb8e0245f052
-- title:
--   Original finite-annulus compensators converge to an actual centred L2 random variable
-- statement:
--   Under summability of the *actual* squared Lévy-band rate energy for a deterministic original-X negative-annulus partition, the finite compensated spatial-simple physical sums have canonical L2 representatives M_k that converge in L2(P) to a centred random variable. This imports Proved finite-family zero-mean/MemLp source d37d4343, Proved squared-integral Cauchy 551cd8d6, Proved real-energy to eLpNorm convergence c63c534b, and Proved completeness/mean passage 05634bad. It is a rigorous original-path small-jump approximation theorem, not an assertion of stopped Ito-Meyer reward or Gaussian same-space construction.
-- source:
--   MIX-INFINITE20 directly assembles original-X finite spatial annulus MemLp/centredness and squared-integral Cauchy results into an Lp(P) limit as an analytic prerequisite for 5f12c023.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf19_original_finite_spatial_annulus_weighted_centered_L2
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf18_original_summable_annulus_partial_sums_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian15_real_squared_energy_to_L2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_L2_cauchy_centered_martingale_limit_L1_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped ENNReal NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf20_original_summable_annulus_centered_L2_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (cut : ℕ → ℕ) (hcut : Monotone cut) (a : ℕ → ℝ) :
    let B : ℕ → Set ℝ := fun i =>
      Ioc (-(1 / ((cut i : ℝ) + 1))) (-(1 / ((cut (i + 1) : ℝ) + 1)))
    let N : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B i)
    let r : ℕ → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let S : ℕ → Ω → ℝ := fun k ω =>
      ∑ i ∈ Finset.range k, a i * ((N i ω).toReal - r i)
    Summable (fun i => (a i) ^ 2 * r i) →
      ∃ M : ℕ → Lp ℝ (2 : ℝ≥0∞) P,
        (∀ k, (M k : Ω → ℝ) =ᵐ[P] S k) ∧
        ∃ L : Lp ℝ (2 : ℝ≥0∞) P,
          Tendsto M Filter.atTop (𝓝 L) ∧
          (∫ ω, L ω ∂P) = 0 := by sorry
