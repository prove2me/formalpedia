-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive
-- name    : AvramDividend.Classical.avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T22:17:57.178639+00:00
-- url     : https://prove2.me/theorems/cc32b5e3-86ff-4342-9ebc-e24f54527a29
-- title:
--   Original top-cap postpayment stopped Gaussian HJB generator Riemann drift is nonpositive
-- statement:
--   The actual original-process postpayment reserve stays strictly positive at each pre-stop deterministic grid time under the two-sided compact prefix, by the already Proved original postpayment-floor lemma. Hence each discounted nonnegative-mesh multiple of generator w(y)-q w(y) is nonpositive, and its finite sum is nonpositive almost surely. Isolates the sign of the source drift from the genuinely difficult Gaussian physical Taylor and stopped-grid error needed for the Open gledger28 source-vs-Gaussian mesh theorem.
-- source:
--   Exact root-connected original Gaussian source-to-martingale decomposition for gledger28 8dcc5100, using Proved postpayment floor cb67c5ea and the target's HJB generator sign. The remaining true analytic step is L1 Taylor/source correction, not another copy of the target expected-reward inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger51_original_postpayment_stopped_generator_grid_nonpositive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let G : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        if s < ρ ω then
          (Δ : ℝ) * Real.exp (-(q * (s : ℝ))) *
            (X.generator w (x + X.X s ω - rightLimit D s ω) -
              q * w (x + X.X s ω - rightLimit D s ω))
        else 0
    ∀ᵐ ω ∂P, G ω ≤ 0 := by sorry
