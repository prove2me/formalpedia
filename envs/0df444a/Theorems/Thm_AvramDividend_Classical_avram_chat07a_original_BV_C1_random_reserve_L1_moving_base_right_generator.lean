-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07a_original_BV_C1_random_reserve_L1_moving_base_right_generator
-- name    : AvramDividend.Classical.avram_chat07a_original_BV_C1_random_reserve_L1_moving_base_right_generator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:06:13.079914+00:00
-- url     : https://prove2.me/theorems/89f7e3c0-00c7-4b81-9bf7-a54b284f79e6
-- title:
--   Original BV Lévy C¹ semigroup generator limit persists under same-source random L¹-small moving reserves
-- statement:
--   For the actual Standing bounded-variation spectrally negative Lévy process, let Z_h be any random reserve on the original sample space, possibly correlated with the source increment X_h. Under the exact Bochner integrability of both random-base source payoffs and an L¹ perturbation envelope whose expected value divided by positive h tends to zero, the right-time derivative of the expected Lévy transition increment evaluated at Z_h equals the canonical generator at fixed x. The pointwise Lipschitz estimate couples the random-base and fixed-base expectations directly on the same original Ω; neither Markov independence of Z_h nor a fictitious Lévy copy is required. This is a genuinely stochastic reserve-localisation interface complementary to the deterministic o(h) result, without claiming the stopped compensator or the HJB verification inequality.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), original-source random reserve localisation. Uses genuinely Proved canonical BV generator derivative b56e7174-ebfe-49ac-899d-0f14fc900201, original BV shifted-payoff integrability c9c0a844-c6f6-4979-bd6b-6001aef874a7, and same-probability-space random reserve L1 Lipschitz stability 00a4032d-5166-4ef1-b066-8082dba47cd3. All nonzero-time integrability premises are explicit; no stopped compensator is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_levy_transition_right_generator_of_global_C1_lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_levy_random_reserve_payoff_L1_stability
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07a_original_BV_C1_random_reserve_L1_moving_base_right_generator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (hgen : X.GeneratorIntegrable w x)
    (Z : ℝ → Ω → ℝ)
    (hInt : ∀ h : ℝ, 0 < h → h < 1 →
      Integrable (fun ω => w (Z h ω + X.X (Real.toNNReal h) ω)) P ∧
      Integrable (fun ω => w (Z h ω)) P ∧
      Integrable (fun ω => L * |Z h ω - x|) P)
    (hRate : Tendsto
      (fun h : ℝ => h⁻¹ * (∫ ω, L * |Z h ω - x| ∂P))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, w (Z h ω + X.X (Real.toNNReal h) ω) ∂P) -
         (∫ ω, w (Z h ω) ∂P)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (X.generator w x)) := by sorry
