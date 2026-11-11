-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger38_original_bounded_stop_discount_mesh_error_L1
-- name    : AvramDividend.Classical.avram_gledger38_original_bounded_stop_discount_mesh_error_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T19:17:10.438844+00:00
-- url     : https://prove2.me/theorems/13ad867d-a95f-4dc5-b1bb-29aa22e7a9e7
-- title:
--   Original stopped discounted dividend mesh quadrature and strict final-cell error vanish in L1
-- statement:
--   For any original admissible dividend strategy and bounded right-continuous-filtration stopping clock, the sum of q times physical grid width times unweighted dividend measure up to the clock and the discounted dividend measure in the shrinking open final clock cell is integrable and tends to zero in L1. This error is explicit, nonnegative and independent of the smooth payoff and Gaussian centring, so it separates measure-theoretic convergence from the finite-cell Ito-Stieltjes inequality. The unweighted component is explicitly strict at the stopped clock and therefore excludes any terminal right-payment atom which admissibility need not bound at ruin.
-- source:
--   Needed analytic error convergence for original stopped topcap cash/source 42bb8ee3. Reuse Proved standing discounted stopped cash integrability de6c04ba and strict masked contact tail tendsto zero 7c53ca0f; hρstop ensures measurable clock; hρbound controls unweighted/discounted conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger38_original_bounded_stop_discount_mesh_error_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0)) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε := by sorry
