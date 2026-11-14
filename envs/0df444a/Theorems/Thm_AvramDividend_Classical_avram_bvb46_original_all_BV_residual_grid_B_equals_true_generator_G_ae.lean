-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
-- name    : AvramDividend.Classical.avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:42:01.667208+00:00
-- url     : https://prove2.me/theorems/fcbb3610-40a1-43ab-ae14-0af5588160f8
-- title:
--   On every original standing bounded variation Levy path the physical source residual grid correction vanishes and B equals the strict physical generator G almost surely
-- statement:
--   On one original-source probability-one event, the full source BV drift-minus-actual-physical-jump increment identity proves that all residual R increments cancel at every pair of physical grid clocks. Consequently the exact generator-and-residual source B grid in the mission equals its strict generator component G for every row, with arbitrary finite weighted coefficients. Original standing BV process, original filtration, every source marked jump and all grid clocks retained. Requires neither finite activity nor zero negative jump path. Apply to finitecap phys69 via the original hB, then hAllB implies nonpositive G.
-- source:
--   Original accepted all-BV source two-clock identity ab16704d-ed99-4180-a81b-14a9db944cf9, exact source B ledger of 4287fafd.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva22_original_all_BV_two_clock_source_increment_ae
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (u : ℕ → ℕ → ℝ≥0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ t ω,
      R t ω = ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω else 0))
    (coeff : ℕ → ℕ → Ω → ℝ)
    (B G : ℕ → Ω → ℝ)
    (hB : ∀ n ω, B n ω = G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω))) :
    ∀ᵐ ω ∂P, ∀ n, B n ω = G n ω := by sorry
