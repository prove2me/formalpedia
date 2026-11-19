-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward81_original_trueclock_HJB_B_nonpositive
-- name    : AvramDividend.Classical.avram_pj_reward81_original_trueclock_HJB_B_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T23:09:46.872389+00:00
-- url     : https://prove2.me/theorems/580336d5-43ea-4336-943e-e03c3b9b90b9
-- title:
--   Original finite-cap stopped compact HJB time-drift is nonpositive at any clock
-- statement:
--   The physical HJB drift term B at a stopped clock rho is nonpositive pointwise. For any prepayment left-limit reserve Y in the compact interior band, the original generator inequality makes the drift integrand nonpositive. The discount exponential and ruin/survival indicator are nonnegative, and outside the band the integrand vanishes. Integrating over the actual clipped physical time measure preserves nonpositivity. No Gaussian term, independence, or extra stochastic premise is used. This is a source-exact subsidiary component of reward80; its proof does not establish the missing stopped Itô pathwise ledger or L1 mesh convergence.
-- source:
--   Original Avram classical P4 HJB generator inequality, true ruin-clipped stopped clock with the full positive-time Lebesgue integral.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward81_original_trueclock_HJB_B_nonpositive
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hCfinite : C ≠ ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (u δ v : ℝ) (hu : 0 < u) (hδ : 0 < δ)
    (huv : u + δ < v) (hvCap : v < C.toReal)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 × Ω → ℝ) (ρ : Ω → ℝ≥0) :
    ∀ ω : Ω,
      (∫ t : ℝ≥0,
        (if t ≤ ρ ω then
          Real.exp (-(q * (t : ℝ))) *
            ((if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0) *
             (if Y (t, ω) ∈ Icc (u + δ) v then
                X.generator w (Y (t, ω)) - q * w (Y (t, ω))
              else 0))
         else 0)
         ∂(((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal)) ≤ 0 := by sorry
