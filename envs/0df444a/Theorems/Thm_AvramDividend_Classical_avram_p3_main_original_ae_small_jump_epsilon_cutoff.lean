-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_ae_small_jump_epsilon_cutoff
-- name    : AvramDividend.Classical.avram_p3_main_original_ae_small_jump_epsilon_cutoff
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:48:40.331247+00:00
-- url     : https://prove2.me/theorems/3a4709e5-3e0d-4edc-8eba-11f85446ef3b
-- title:
--   Actual original BV sample paths admit positive epsilon-small negative-jump cutoff
-- statement:
--   On one original-process P-full event, for each fixed finite horizon and every ε>0, the total raw negative left-jump magnitude across the genuine source interval (0,T] below a sufficiently small positive threshold δ is less than ε. It instantiates the published P3-A actual raw jump absolute-summability interface and the exact P3-Main finite-exclusion/positive-cutoff transport, keeping the same Ω,P,𝓕,X and original left limits. Does not invoke a surrogate compound-Poisson process or zero residual premise.
-- source:
--   Source Proved avram_p3_a_bvdrift_original_absolute_raw_jump_interval_summable 54643412-7eb2-4fdf-8178-97b28f1ab720; public P3-Main unconditional epsilon cutoff request 7d095126; P3-D/P3-C interface 1 and 5.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators

theorem AvramDividend.Classical.avram_p3_main_original_ae_small_jump_epsilon_cutoff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      let j : ℝ≥0 → ℝ := fun u =>
        if 0 < u ∧ u ≤ T then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω
        else 0
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          (∑' u : ℝ≥0, if |j u| < δ then |j u| else 0) < ε := by sorry
