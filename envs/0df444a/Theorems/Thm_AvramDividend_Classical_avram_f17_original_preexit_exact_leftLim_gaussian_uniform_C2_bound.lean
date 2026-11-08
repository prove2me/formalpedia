-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
-- name    : AvramDividend.Classical.avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:35:52.299096+00:00
-- url     : https://prove2.me/theorems/4586943e-33c1-4325-a9c6-8e3512cbf987
-- title:
--   Original clipped Gaussian C2 coefficients are uniformly bounded at the exact Function.leftLim reserve used by stopped Ito cells
-- statement:
--   On the actual original controlled Levy reserve, before a genuine countably observed compact-band exit, the exact Function.leftLim reserve used in Gaussian stopped Ito integrands belongs to the same strict C2 band and has uniform discounted gradient and Hessian bounds. The result removes the existential-left-limit mismatch using the pinned leftLim_eq_of_tendsto identity and a positive-time left-neighbourhood nonempty instance, bridging the already Proved F17 original source bounds to the exact stochastic cell integrands.
-- source:
--   Source-faithful exact Function.leftLim adapter of newly Proved F17 existential-limit band Gaussian bounds using pinned Mathlib leftLim_eq_of_tendsto and nhdsWithin_Iio_neBot' at strictly positive time; no stochastic surrogate or additional assumptions.

import Mathlib
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Topology.Order.DenselyOrdered
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_leftlimit_gaussian_uniform_C2_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
              upper < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          y ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH := by sorry
