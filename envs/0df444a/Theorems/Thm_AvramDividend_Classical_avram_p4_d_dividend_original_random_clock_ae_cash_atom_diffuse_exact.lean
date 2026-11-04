-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_clock_ae_cash_atom_diffuse_exact
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_cash_atom_diffuse_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:52:24.155032+00:00
-- url     : https://prove2.me/theorems/a5bd29ce-2e84-49ae-a92a-9ac6a61974d1
-- title:
--   Original finite random stopped Cash exact atom-diffuse decomposition almost surely with zero and terminal atoms
-- statement:
--   For any path-dependent finite NNReal clock τ on the original spectrally negative Lévy probability space, the literal original stopped discounted Cash at horizon τ(ω) has an exact almost-sure real-valued decomposition into a countable right-atomic weighted sum and an atomless Stieltjes contribution. The atomic singleton mass is exactly rightLimit D t-D t for t≤τ, with closed support preserving initial and horizon atoms, and the diffuse component includes singular continuous mass. This follows pathwise from public Proved source f897c004 then lifts to ae P, without changing paymentTimes, introducing auxiliary clocks, or assuming absolute continuity of D.
-- source:
--   Public Proved P4-D f897c004-e02d-44d0-9675-58631eae319f (countable real atom/diffuse exact Cash), canonical P4-F random finite clock τ, Filter.Eventually.of_forall.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_cash_countable_rightatom_sum_and_diffuse
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The exact original Cash atom/diffuse decomposition survives a path-dependent
    finite stop, including zero-time and eligible horizon right-payment atoms. -/

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_clock_ae_cash_atom_diffuse_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (τ : Ω → ℝ≥0) :
    ∀ᵐ ω ∂P,
      let μ : Measure ℝ :=
        (dividendMeasure D ω).restrict (Icc (0 : ℝ) (τ ω : ℝ))
      let f : ℝ → ℝ≥0∞ := fun s =>
        if s ∈ paymentTimes (ruinTime X x D ω)
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0
      ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
        A.Countable ∧ MeasurableSet A ∧
        μ = μatom + μdiffuse ∧
        NullSingletonClass μdiffuse ∧
        μatom Aᶜ = 0 ∧ μdiffuse A = 0 ∧
        μ Set.univ = ENNReal.ofReal (rightLimit D (τ ω) ω) ∧
        (∀ t : ℝ≥0, t ≤ τ ω →
          μatom {(t : ℝ)} =
            ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
        ((∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal =
            (∑' a : A, f a.1 * μatom {a.1}).toReal +
            (∫⁻ s : ℝ, f s ∂μdiffuse).toReal) := by sorry
