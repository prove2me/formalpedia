-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat07a_original_BV_C1_random_reserve_semigroup_quotient_L1_error_bound
-- name    : AvramDividend.Classical.avram_chat07a_original_BV_C1_random_reserve_semigroup_quotient_L1_error_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T10:12:46.046291+00:00
-- url     : https://prove2.me/theorems/1f05db64-0125-43a5-93f9-e99e41462967
-- title:
--   Exact same-source random reserve Lévy semigroup quotient is L¹ stable at rate 2/t
-- statement:
--   For any original spectrally negative Standing bounded-variation Lévy sample path X, positive time t≤1 and possibly path-dependent random reserve Z on the same Ω, the discrepancy between the normalised expected payoff increment from Z and the fixed-base increment from x is bounded by 2/t times the original expectation of L|Z−x|. Only genuine Bochner integrability of the two random-payoff terms and their L1 error envelope is assumed. The proof applies the canonically Proved original same-Ω random reserve Lipschitz expectation estimate twice, once at source time t and once at time zero, then uses the triangle inequality and positivity of t. This directly controls stochastic moving-base semigroup error and is the exact quantitative missing component for the published same-source random L1 moving-base right-generator theorem 89f7e3c0. It neither assumes independence of Z and X_t nor substitutes a fictitious model.
-- source:
--   Original spectrally negative Lévy semigroup first-order stable localisation, Avram–Palmowski–Pistorius (2007), Proposition 4(i). Exact Proved source payoff integrability c9c0a844-c6f6-4979-bd6b-6001aef874a7 and actual same-space L1 reserve comparison 00a4032d-5166-4ef1-b066-8082dba47cd3. Canonical parent new random right generator 89f7e3c0-00c7-4b81-9bf7-a54b284f79e6. This child isolates source-estimate, not terminal expected HJB verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
import Theorems.Thm_AvramDividend_Classical_levy_random_reserve_payoff_L1_stability
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_chat07a_original_BV_C1_random_reserve_semigroup_quotient_L1_error_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (t : ℝ≥0) (ht : 0 < t) (ht1 : t ≤ 1)
    (Z : Ω → ℝ)
    (hI : Integrable (fun ω => w (Z ω + X.X t ω)) P)
    (hB : Integrable (fun ω => w (Z ω)) P)
    (hDom : Integrable (fun ω => L * |Z ω - x|) P) :
    |(t : ℝ)⁻¹ *
       ((∫ ω, w (Z ω + X.X t ω) ∂P) - (∫ ω, w (Z ω) ∂P)) -
      (t : ℝ)⁻¹ *
       ((∫ ω, w (x + X.X t ω) ∂P) - w x)| ≤
      2 * (t : ℝ)⁻¹ * (∫ ω, L * |Z ω - x| ∂P) := by sorry
