-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb42_original_Standing_BV_finiteactivity_weak_C1_zero_boundary_HJB_sign
-- name    : AvramDividend.Classical.avram_bvb42_original_Standing_BV_finiteactivity_weak_C1_zero_boundary_HJB_sign
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T18:31:54.386204+00:00
-- url     : https://prove2.me/theorems/e6ed1cc3-24fb-4e84-9fd2-be4cc7e46d18
-- title:
--   Original Standing BV finiteactivity weak-C1 one-sided zero-boundary compensated physical HJB sign
-- statement:
--   Rigorous original one-sided HJB boundary limit at zero reserve for finite-negative-jump-intensity Standing bounded-variation spectrally negative Lévy driver, positive q, w continuous on [0,∞), w(z)=0 for z<0, true HJB generator nonpositive and derivative ≥1 for 0<y<C. Prove original d+∫_{z<0}[w(z)-w(0)]ν(dz)−q w(0)≤0 WITHOUT extra assumptions w(0)≥0 or ContDiffOn ℝ 1 w on (0,C). Analytic route: original BV physical generator interior = d*w′(y)+κ(y), d>0 from Standing BV, w′(y)≥1, hence d+κ(y)−qw(y)≤0; as y→0+, w(y)→w(0), κ(y)→κ(0) by finite ν, w(z)=0 for z<0 and w continuous at 0, almost-everywhere dominated convergence (plus atomlessness of ν under Standing). The weak sign is precisely the remaining original zero-plateau cash lemma source and avoids silently importing unavailable smoothness.
-- source:
--   Original Proved BV physical generator identity c8ba98f0, Standing BV drift positivity 0432f641 and diffuse ν bc92b9ce; finiteactivity dominated-convergence, original zero boundary HJB 0344aae3 (stronger hypotheses), w negative reserve zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb42_original_Standing_BV_finiteactivity_weak_C1_zero_boundary_HJB_sign
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    X.drift +
      (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν) -
      q * w 0 ≤ 0 := by sorry
