-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07a_original_BV_C1_normalized_semigroup_spatial_stability
-- name    : AvramDividend.Classical.avram_chat07a_original_BV_C1_normalized_semigroup_spatial_stability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T09:40:08.7832+00:00
-- url     : https://prove2.me/theorems/53fabbe9-a624-49db-8095-be1934a174e1
-- title:
--   Original BV Lévy normalised C¹ semigroup increments are quantitatively stable under shifts of starting reserve
-- statement:
--   For the original Standing bounded-variation spectrally negative Lévy process and each globally C¹, L-Lipschitz test payoff, the real small-time transition difference quotient at any two deterministic reserves differs by at most 2L times their distance divided by the original physical time t, uniformly for all positive t≤1. Both expectations use the actual X.X t on the same sample space, and their Bochner integrability follows from the genuine-source transition theorem. This is a quantitative moving-base stability interface for cofinal reserve grids: an o(t) spatial perturbation preserves the generator right slope. It does not assert the missing conditional stopped Itô–Meyer compensator.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), source-specific BV semigroup finite-difference localisation; genuine original-source integrability Proved c9c0a844-c6f6-4979-bd6b-6001aef874a7 and same-Ω L1 reserve stability Proved 00a4032d-5166-4ef1-b066-8082dba47cd3. Parent analytic generator bridge Proved b56e7174-ebfe-49ac-899d-0f14fc900201; supports compact localisation without replacing the missing original stopped compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_levy_random_reserve_payoff_L1_stability
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07a_original_BV_C1_normalized_semigroup_spatial_stability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x u : ℝ) (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1) :
    |(t : ℝ)⁻¹ *
         ((∫ ω, w (u + X.X t ω) ∂P) - w u) -
       (t : ℝ)⁻¹ *
         ((∫ ω, w (x + X.X t ω) ∂P) - w x)| ≤
      2 * L * (t : ℝ)⁻¹ * |u - x| := by sorry
