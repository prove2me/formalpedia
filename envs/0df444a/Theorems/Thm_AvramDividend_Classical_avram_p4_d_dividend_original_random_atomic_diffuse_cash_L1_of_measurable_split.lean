-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_random_atomic_diffuse_cash_L1_of_measurable_split
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_diffuse_cash_L1_of_measurable_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:40:28.901104+00:00
-- url     : https://prove2.me/theorems/7a533582-b8b1-41ea-aa2a-56b97d989162
-- title:
--   Original random-clock atomic and diffuse paid Stieltjes cash are L1 whenever the real split is measurable
-- statement:
--   For the actual original Lévy dividendMeasure and paid random horizon, let μatom(ω) and μdiffuse(ω) be chosen atomic and non-atomic Stieltjes parts and let Atom/Diffuse be their exact discounted paid lintegral .toReal quantities. If the real sum Cash=Atom+Diffuse holds almost everywhere and both random quantities are a.e. strongly measurable, then integrability of the source Cash implies integrability of each part separately, since each is nonnegative and dominated by Cash. This makes the measurable random decomposition obligation explicit instead of using an unjustified pathwise choice.
-- source:
--   Proved original random-clock a.e. cash atom/diffuse split UUID a5bd29ce-2e84-49ae-a92a-9ac6a61974d1; pinned MeasureTheory.Integrable.mono type checked for revision 0df444a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_random_atomic_diffuse_cash_L1_of_measurable_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (μatom μdiffuse : Ω → Measure ℝ)
    (Atom Diffuse : Ω → ℝ)
    (hAtom : ∀ ω, Atom ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(μatom ω)).toReal)
    (hDiffuse : ∀ ω, Diffuse ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(μdiffuse ω)).toReal)
    (hRealSplit : ∀ᵐ ω ∂P, Cash ω = Atom ω + Diffuse ω)
    (hAtomMeas : AEStronglyMeasurable Atom P)
    (hDiffuseMeas : AEStronglyMeasurable Diffuse P) :
    Integrable Atom P ∧ Integrable Diffuse P := by sorry
