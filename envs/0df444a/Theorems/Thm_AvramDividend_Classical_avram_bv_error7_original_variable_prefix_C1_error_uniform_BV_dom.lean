-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_variable_prefix_C1_error_uniform_BV_dom
-- name    : AvramDividend.Classical.avram_bv_error7_original_variable_prefix_C1_error_uniform_BV_dom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:31:52.6791+00:00
-- url     : https://prove2.me/theorems/24aa95b9-3b08-4a85-8a2e-c372abe21399
-- title:
--   Uniform genuine BV source mass domination for original variable-horizon physical C1 errors
-- statement:
--   For every actual bounded-variation Lévy sample path outside one null set, all original dividend-controlled physical clock prefixes from zero to any sample-dependent endpoint at most fixed T satisfy a uniform bound on the full signed discounted C1 Taylor residual. Under exact compact-band Lipschitz and derivative hypotheses, the residual magnitude is bounded by 2L times the genuine fixed-T source mass |drift|T+|T drift-X_T|. The proof combines the source-exact compact Taylor cell bound with the newly proved variable-prefix jump-removed total variation bound and is independent of stochastic cash/prebudget.
-- source:
--   Direct adaptation of already Proved global_I theorem 12895109, replacing only the exact fixed-endpoint Y variation import by its variable-prefix extension 2a0c3e31. This is the uniform L1 domination half of the original 2bc848f9 positive-error convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_prefix_Y_variation_le_full_horizon_mass
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_compact_Taylor_cell_bound_of_lipschitz_and_deriv
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_original_variable_prefix_C1_error_uniform_BV_dom
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (a b L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Set.Icc a b, ∀ z ∈ Set.Icc a b,
      |w z - w y| ≤ L * |z - y|)
    (hDeriv : ∀ y ∈ Set.Icc a b, |deriv w y| ≤ L)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0) (n : ℕ),
      u 0 = 0 → u n ≤ T →
      (∀ i, i < n → u i ≤ u (i + 1)) →
      (let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω
        else 0
       let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
       let z : ℕ → ℝ := fun i =>
         x + X.X (u i) ω - rightLimit D (u i) ω
       let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
       (∀ i, i < n →
         Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
       |∑ i ∈ Finset.range n,
          Real.exp (-(q * (u i : ℝ))) *
            (w (z i + c i) - w (z i) - deriv w (z i) * c i)| ≤
         (2 * L) * (|X.drift| * (T : ℝ) +
           |(T : ℝ) * X.drift - X.X T ω|)) := by sorry
