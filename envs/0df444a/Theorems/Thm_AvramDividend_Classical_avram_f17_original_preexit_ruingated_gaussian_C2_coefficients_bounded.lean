-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_ruingated_gaussian_C2_coefficients_bounded
-- name    : AvramDividend.Classical.avram_f17_original_preexit_ruingated_gaussian_C2_coefficients_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:47:20.543898+00:00
-- url     : https://prove2.me/theorems/a596c8bd-d198-4187-ad06-446646cb2476
-- title:
--   Original pre-exit Gaussian coefficient with the exact source Hessian interior mask is uniformly bounded
-- statement:
--   For the original zero-jump unbounded-variation Levy reserve observed before its genuine compact-band exit, the exact left-limit reserve is in the strict positive cap domain. The stopped Gaussian gradient and the precisely gated Hessian coefficient appearing in existing original source Ito mesh theorems are uniformly discounted-bounded by one pair of constants. The proof uses previously Proved exact original Function.leftLim band and C2 bounds and preserves all physical clock, cap and dividend semantics.
-- source:
--   Exact original-source interior-mask bridge to the Hessian integrand in original stopped C2 Gaussian one-cell and finite-mesh expectation identities, using public Proved F17 exact Function.leftLim band theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_preexit_exact_leftLim_gaussian_uniform_C2_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem AvramDividend.Classical.avram_f17_original_preexit_ruingated_gaussian_C2_coefficients_bounded
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
          (0 < y ∧ ENNReal.ofReal y < C) ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) *
              (if 0 < y ∧ ENNReal.ofReal y < C
               then iteratedDeriv 2 w y else 0)| ≤ KH := by sorry
