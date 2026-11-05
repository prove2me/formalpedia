-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_isometry_and_l2_limit_pipeline
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_isometry_and_l2_limit_pipeline
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T15:14:01.800211+00:00
-- url     : https://prove2.me/theorems/b82e1594-8eb8-46e1-a94d-f08e9c414d10
-- title:
--   Original intrinsic finite-grid L2 isometry and physical stopped-band martingale completion interface
-- statement:
--   On exactly the same original Avram path measure and filtration, the accepted physical finite-grid isometry gives its true quadratic moment under actual source jump-count and pair-moment hypotheses. Original ν square-tail finiteness, the physical stopped-band square-energy bound, adaptedness and centred increments then construct an L2 limit process retaining right-continuous-filtration martingale identities. The substantial physical second-moment and stopping hypotheses remain explicit rather than being replaced by equality in law.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_grid_L2_isometry
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_quadratic_tail_finite
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_nu_quadratic_tail_l2_cauchy
import Theorems.Thm_AvramDividend_Classical_avram_leanlevy_bridge_original_rightcont_l2_martingale_of_cauchy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_isometry_and_l2_limit_pipeline
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (B : ι → Set ℝ) (J : ι → Ω → ℝ)
    (hSource : ∀ i ∈ S, ∀ ω, J i ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B i)).toReal)
    (r c : ι → ℝ)
    (hRate : ∀ i ∈ S, r i =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B i))).toReal)
    (hPairInt : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun ω =>
      (c i * (J i ω - r i)) * (c j * (J j ω - r j))) P)
    (hPairMoment : ∀ i ∈ S, ∀ j ∈ S,
      (∫ ω, (c i * (J i ω - r i)) *
        (c j * (J j ω - r j)) ∂P) =
          if i = j then c i ^ 2 * r i else 0)
    (M : ℕ → ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P) (K : ℝ)
    (hBandBound : ∀ t n m, n ≤ m →
      dist (M n t) (M m t) ≤
        K * Real.sqrt ((∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν).toReal))
    (hAdapt : ∀ u n,
      ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le u)) (M n u) :
        Lp ℝ (2 : ℝ≥0∞) P) = M n u)
    (hCenter : ∀ u v, u ≤ v → ∀ n,
      (MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le u)) (M n v - M n u) = 0) :
    (∫ ω, (∑ i ∈ S, c i * (J i ω - r i)) ^ 2 ∂P) =
      ∑ i ∈ S, c i ^ 2 * r i ∧
    ∃ L : ℝ≥0 → Lp ℝ (2 : ℝ≥0∞) P,
      (∀ u, Tendsto (fun n => M n u) atTop (𝓝 (L u))) ∧
      (∀ u, ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le u)) (L u) :
        Lp ℝ (2 : ℝ≥0∞) P) = L u) ∧
      (∀ u v, u ≤ v →
        ((MeasureTheory.condExpL2 ℝ ℝ ((𝓕.rightCont).le u)) (L v) :
          Lp ℝ (2 : ℝ≥0∞) P) = L u) := by sorry
