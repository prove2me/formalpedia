-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_true_horizon_completed_survival_integral_balance_no_standing
-- name    : AvramDividend.Classical.p2m81_bv_true_horizon_completed_survival_integral_balance_no_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T23:44:52.059749+00:00
-- url     : https://prove2.me/theorems/bf32e92b-fc45-4d62-91a3-784602809c72
-- title:
--   Standing-free BV completed upper-first and surviving horizon killed reward expectation balance
-- statement:
--   The explicit sum of genuine original Levy completed upper-first discounted scale reward and surviving finite-horizon discounted scale reward is Bochner integrable and has expectation Wq(x) under BV with a positive Esscher root X.psi phi = q, with no Standing assumption and no mesh or moment assumptions. This is the standing-free analogue of avram_ws01b_bv_true_horizon_completed_survival_integral_balance, replacing Standing by the root hypothesis; it is the single missing premise for the standing-free BV stopped-scale balance Kyprianou Ch08 StageB p2m81.
-- source:
--   Standing-free BV finite-horizon S-balance: drift positivity from the Esscher root via the BV Laplace rearrangement, then an epsilon-down-barrier discrete-grid martingale with exit-time continuity limit. Parent Kyprianou.Ch08.StageB.p2m81_bv_stopped_scale_balance_no_standing_public (3c45c728) replays the two accepted standing proofs 3cd88d0e and 322217fe with every other step already Proved standing-free; this child is the only step with no standing-free form. Near-misses f8432a5a (standing BV) and 36dd3377 (UBV) are inapplicable by hypothesis mismatch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_true_horizon_completed_survival_integral_balance_no_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) :
    (let S : Ω → ℝ := fun ω =>
      let U : ℝ≥0∞ := twoSidedExitUpTime X (a-x) ω
      let D : ℝ≥0∞ := twoSidedExitDownTime X (-x) ω
      (if U < D ∧ U.toNNReal ≤ T then
        Real.exp (-(q * (U.toNNReal : ℝ))) * W (x + X.X U.toNNReal ω)
      else 0) +
      (if (T : ℝ≥0∞) < U ∧ (T : ℝ≥0∞) < D then
        Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
      else 0);
    Integrable S P ∧ (∫ ω, S ω ∂P) = W x) := by sorry
