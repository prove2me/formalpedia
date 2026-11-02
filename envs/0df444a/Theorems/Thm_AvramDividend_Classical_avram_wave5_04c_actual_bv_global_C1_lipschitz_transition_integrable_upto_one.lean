-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:53:55.137794+00:00
-- url     : https://prove2.me/theorems/c9c0a844-c6f6-4979-bd6b-6001aef874a7
-- title:
--   Original BV Lévy transition expectation is integrable for every globally Lipschitz C1 payoff at small time
-- statement:
--   For the actual original spectrally negative Lévy X, with precisely its canonical Standing and BoundedVariation, any globally Lipschitz continuously differentiable payoff w satisfies Integrable (fun ω => w (x+X.X t ω)) P at every original source time t≤1, without an assumed generator identity or constructed process. The already Proved source X_t first-moment integrability and global Lipschitz bound imply |w(x+X_t)|≤|w x|+L|X_t|. ContDiff gives Borel measurability; the RHS is integrable under X.isProbability, so Integrable.mono' yields the result. This is the exact expectation-domain prerequisite for the canonical global C1 BV generator-semigroup theorem, not its full derivative identity.
-- source:
--   Complete source candidates/work_on/AvramDividend_04c_actual_C1_payoff_integrable_upto_one_probe.lean remotely private-probe compiler verified without source diagnostics; not yet proof submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_source_X_integrable_upto_one
set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_global_C1_lipschitz_transition_integrable_upto_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (w : ℝ → ℝ) (hwC1 : ContDiff ℝ 1 w)
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |w u - w v| ≤ L * |u - v|)
    (x : ℝ) (t : ℝ≥0) (ht : t ≤ 1) :
    Integrable (fun ω => w (x + X.X t ω)) P := by sorry
