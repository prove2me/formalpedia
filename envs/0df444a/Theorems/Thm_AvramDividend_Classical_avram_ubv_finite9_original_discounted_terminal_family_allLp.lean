-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_discounted_terminal_family_allLp
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_discounted_terminal_family_allLp
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T10:16:25.433557+00:00
-- url     : https://prove2.me/theorems/dce3e97e-4f90-413f-831e-86efbf9b3506
-- title:
--   All Lp moments for the original finite-cap stopped terminal family
-- statement:
--   A common finite-cap L∞ envelope for every discounted source-exact post-right-payment/ruin terminal reward, plus a.e. strong measurability, yields MemLp for every index and arbitrary ENNReal exponent p, including p=2. This does not assert a moment bound on derivatives of w or the stochastic compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_discounted_terminal_family_allLp
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : ℕ → Ω → ℝ≥0) (W Term : ℕ → Ω → ℝ)
    (hW : ∀ k ω, W k ω =
      if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
      else riskProcess X x D (σ k ω) ω)
    (q : ℝ) (hq : 0 ≤ q)
    (hTerm : ∀ k ω, Term k ω =
      Real.exp (-(q * (σ k ω : ℝ))) * w (W k ω))
    (hTermMeas : ∀ k, AEStronglyMeasurable (Term k) P) :
    ∀ p : ℝ≥0∞, ∀ k : ℕ, MemLp (Term k) p P := by sorry
