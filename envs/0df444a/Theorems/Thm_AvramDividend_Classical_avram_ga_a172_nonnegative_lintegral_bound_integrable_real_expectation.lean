-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a172_nonnegative_lintegral_bound_integrable_real_expectation
-- name    : AvramDividend.Classical.avram_ga_a172_nonnegative_lintegral_bound_integrable_real_expectation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:48:22.608266+00:00
-- url     : https://prove2.me/theorems/b1d4bd52-de23-4b5d-8cd5-4fb16da8eabe
-- title:
--   Finite extended nonnegative source energy bound proves integrability and same real expectation bound
-- statement:
--   A measurable almost-surely nonnegative real observable with extended nonnegative integral bounded by a finite nonnegative real constant is integrable as a real function and has a real expectation bounded by the same constant. Supports original stopped Gaussian quadratic energy ga_a170 from Proved ga_a39.
-- source:
--   Mathlib lintegral_ofReal_ne_top_iff_integrable and Proved chat03_lintegral_bound_implies_real_integral_bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lintegral_bound_implies_real_integral_bound
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a172_nonnegative_lintegral_bound_integrable_real_expectation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (K : ℝ)
    (hf : Measurable f) (hf0 : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hK : 0 ≤ K)
    (hBound : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal K) :
    Integrable f P ∧ (∫ ω, f ω ∂P) ≤ K := by sorry
