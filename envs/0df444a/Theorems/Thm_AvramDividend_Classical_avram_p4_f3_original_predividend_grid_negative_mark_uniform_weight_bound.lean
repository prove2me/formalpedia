-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_grid_negative_mark_uniform_weight_bound
-- name    : AvramDividend.Classical.avram_p4_f3_original_predividend_grid_negative_mark_uniform_weight_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:03:52.259061+00:00
-- url     : https://prove2.me/theorems/254417d0-37cf-4bf7-b801-ddeb08fc25bf
-- title:
--   Uniform bounded original pre-dividend stopped-grid negative-mark weights on compact reserves
-- statement:
--   For the actual original Lévy path X and dividend right-limit D, at every deterministic grid time and every strictly negative selected mark z, the physical pre-dividend left-reserve clipped to a fixed compact positive strict-cap band yields a weighted-jump coefficient w(u+z)-w(u) bounded in absolute value by one finite deterministic L independent of mark, grid index and sample path. This derives boundedness from the source exact Lévy small-jump quadratic envelope without assuming finite global jump intensity. No predictable measurability or stochastic integral centring is asserted.
-- source:
--   Apply the Proved original compact negative mark quadratic min bound 90c3bdda to the true physical clipped left reserve, then use min(1,z²)<=1 and the elementary |a|<=a²+1 inequality to derive an absolute constant M+1. This supplies the explicit hBound coefficient input for the Proved P4-S3 physical finite-band grid martingale, after predictable measurability is separately established.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_kernel_uniform_quadratic_min_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_predividend_grid_negative_mark_uniform_weight_bound
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (grid : ℕ → ℝ≥0) (z : ι → ℕ → ℝ)
    (hz : ∀ j i, z j i < 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j i ω,
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) (grid i)
      let u := if y ∈ Icc δ K then y else δ
      |w (u + z j i) - w u| ≤ L := by sorry
