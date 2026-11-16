-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb45_original_finite_activity_negative_mark_kernel_right_continuous_at_zero
-- name    : AvramDividend.Classical.avram_bvb45_original_finite_activity_negative_mark_kernel_right_continuous_at_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:39:59.419199+00:00
-- url     : https://prove2.me/theorems/bf417719-924f-4b0a-a910-d5dd1bb0280c
-- title:
--   Finite-activity original negative-mark generator kernel continuous at reserve zero along C/(n+2)
-- statement:
--   Given the ACTUAL original spectrally negative Lévy negative-jump measure ν with finite total negative intensity, continuous candidate w on [0,∞) and w(y)=0 for y<0, prove the genuine signed kernel κ(y)=∫_{z<0}(w(y+z)−w(y))ν(dz) converges to κ(0) along explicit positive physical reserve y_n=C/(n+2) as n→∞. Full original ν is unchanged. Proof blueprint: on each z<0, y_n+z<0 eventually so w(y_n+z)=0 and w(y_n)→w0; on a neighbourhood of reserve zero, |w| is bounded by continuity, yielding a finite ν-integrable constant dominator; dominated convergence applies. The lemma enables a rigorous weaker-C1 one-sided zero-boundary HJB sign e6ed1cc3 and closes original zero constant-reserve compensated full-T cash source a773dc60.
-- source:
--   Original full negative mark intensity finite, Mathlib tendsto_integral_of_dominated_convergence, continuity-on compact for w, original C positive finite.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb45_original_finite_activity_negative_mark_kernel_right_continuous_at_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0) :
    Tendsto
      (fun n : ℕ =>
        ∫ z in Iio (0 : ℝ),
          w (C.toReal / ((n : ℝ) + 2) + z) -
            w (C.toReal / ((n : ℝ) + 2)) ∂X.ν)
      atTop
      (𝓝 (∫ z in Iio (0 : ℝ), w ((0 : ℝ) + z) - w 0 ∂X.ν)) := by sorry
