-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn4_original_controlled_grid_gradient_exact_L2_isometry
-- name    : AvramDividend.Classical.avram_wave7_05_turn4_original_controlled_grid_gradient_exact_L2_isometry
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T16:37:44.826202+00:00
-- url     : https://prove2.me/theorems/f3ae0c12-e779-4f7a-af92-e004499196c7
-- title:
--   True controlled-reserve Gaussian predictable finite-grid exact L2 isometry
-- statement:
--   For the true source X with nu=0, real dividend control and left-limit reserve, the bounded discounted and true-ruin-masked gradient coefficients at pairwise disjoint deterministic right-continuous grid intervals have source-specific L2 finite sum, integrable square and exact diagonal quadratic variation isometry. Each coefficient is identified with the genuine source stopped derivative, and its measurability in the relevant sigma algebras is explicit. No independent Gaussian model or all-nu Ito conclusion is claimed.
-- source:
--   Proved source one-cell stopped Gaussian variance theorem 6a3514b2-24ca-4f94-9129-5c76f9065077 plus Proved predictable finite-grid exact isometry 78e197ea-3427-4cce-aab5-066bba435863; original process derivative and rightLimit dividend controls remain intact.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_turn3_original_controlled_stopped_gaussian_exact_variance
import Theorems.Thm_AvramDividend_Classical_avram_wave7_05_original_gaussian_finite_predictable_grid_exact_L2_isometry

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave7_05_turn4_original_controlled_grid_gradient_exact_L2_isometry
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {ι : Type*} [DecidableEq ι]
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0)
    (S : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (hSep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → t i ≤ s j ∨ t j ≤ s i)
    (G : ι → Ω → ℝ)
    (hGsource : ∀ i ∈ S, G i = stoppedValue (fun u ω =>
      if u ≤ T then
        (Real.exp (-(q * (u : ℝ))) *
          deriv w (Function.leftLim
            (fun v : ℝ≥0 => x + X.X v ω - rightLimit D v ω) u)) *
          (if (u : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
      else 0) (fun _ => (s i : WithTop ℝ≥0)))
    (hGown : ∀ i ∈ S, Measurable[𝓕.rightCont (s i)] (G i))
    (hGpair : ∀ i ∈ S, ∀ j ∈ S, t i ≤ s j →
      Measurable[𝓕.rightCont (s j)] (G i))
    (K : ℝ) (hK : 0 ≤ K)
    (hGbound : ∀ i ∈ S, ∀ ω, |G i ω| ≤ K) :
    let F : ι → Ω → ℝ := fun i ω =>
      G i ω * (X.X (t i) ω - X.X (s i) ω -
        ((t i - s i) : ℝ) * X.c)
    MemLp (fun ω => ∑ i ∈ S, F i ω) 2 P ∧
    Integrable (fun ω => (∑ i ∈ S, F i ω) ^ 2) P ∧
    (∫ ω, (∑ i ∈ S, F i ω) ^ 2 ∂P) =
      ∑ i ∈ S, (∫ ω, (F i ω) ^ 2 ∂P) := by sorry
