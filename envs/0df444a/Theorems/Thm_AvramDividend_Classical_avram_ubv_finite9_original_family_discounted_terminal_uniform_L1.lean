-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_family_discounted_terminal_uniform_L1
-- name    : AvramDividend.Classical.avram_ubv_finite9_original_family_discounted_terminal_uniform_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:42:29.881901+00:00
-- url     : https://prove2.me/theorems/f8468989-b5c0-4281-a2e0-f60a615b3ecc
-- title:
--   Uniform discounted original stopped terminal bound and L1 integrability across localisation indices
-- statement:
--   The original post-right-payment/ruin stopped terminal reward admits one deterministic finite-cap L∞ bound across all localisation indices; when each exact terminal component is strongly measurable, all are integrable. The bound is uniform in k, independent of individual stopped clocks, and preserves the time-zero and ruin alternatives. It supports the terminal UI and dominated-convergence stage of the finite-cap Ito–Meyer proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_finite9_original_family_discounted_terminal_uniform_L1
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
    ∃ B : ℝ, 0 ≤ B ∧ (∀ k ω, |Term k ω| ≤ B) ∧
      (∀ k, Integrable (Term k) P) := by sorry
