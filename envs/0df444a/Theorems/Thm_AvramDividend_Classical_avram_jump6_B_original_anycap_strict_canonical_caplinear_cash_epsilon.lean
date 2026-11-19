-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
-- name    : AvramDividend.Classical.avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:28:39.889874+00:00
-- url     : https://prove2.me/theorems/ce331276-5b54-4120-8898-d9719b10a70b
-- title:
--   True original any-cap strict pre-ruin physical-grid paid cash and caplinear source budget is asymptotically nonpositive
-- statement:
--   For the unchanged original Lévy X and admissible D with any finite/infinite positive dividend cap, the stopped original true closed-Iic paid cash plus the initial cap-linear postpayment potential correction minus the actual discounted physical-grid pre/postpayment caplinear potential drops is eventually at most arbitrary positive epsilon at every strictly pre-ruin bounded stopped clock. Derived from the newly Proved all-cap canonical Stieltjes signed source bound and original vanishing mesh error. This is the source-exact caplinear asymptotic ledger needed to separate the remaining finite-cap w-versus-V previsible defect.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anycap_strict_each_grid_caplinear_signed_cash
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_canonical_discount_error_finite_and_vanishing
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anycap_strict_canonical_caplinear_cash_epsilon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (hStrict : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n : ℕ) (ht : t ≤ (n : ℝ≥0)) :
    let v : ℕ → ℕ → ℝ≥0 := fun j i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
    let Cash : ℝ≥0∞ :=
      ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (t : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop,
      Cash.toReal + (V (x - rightLimit D 0 ω) - V x) -
        (∑ i ∈ Finset.range (m j),
          Real.exp (-(q * (v j (i + 1) : ℝ))) *
          (V (x + X.X (v j (i + 1)) ω - rightLimit D (v j i) ω) -
            V (x + X.X (v j (i + 1)) ω - rightLimit D (v j (i + 1)) ω)))
        ≤ ε := by sorry
