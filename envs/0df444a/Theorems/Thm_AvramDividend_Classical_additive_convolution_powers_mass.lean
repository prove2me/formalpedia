-- Prove2me | Theorems.Thm_AvramDividend_Classical_additive_convolution_powers_mass
-- name    : AvramDividend.Classical.additive_convolution_powers_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:27:22.893642+00:00
-- url     : https://prove2.me/theorems/352796af-cbe5-476b-86e8-f47bd591bd96
-- title:
--   Total mass of additive convolution power equals power of kernel mass
-- statement:
--   For an SFinite measure κ on ℝ and the recursively defined additive convolution powers m_0=Dirac(0), m_(n+1)=κ∗m_n, with SFinite m_n, show the total mass m_n(ℝ) equals κ(ℝ)^n. Prove by induction, using the pinned Mathlib lintegral_conv for constant function one (which gives total mass multiplicativity of convolution). This is the final generic mass identity needed for a strictly subcritical Esscher tilted geometric renewal series.
-- source:
--   Pinned Mathlib MeasureTheory.Measure.lintegral_conv (to_additive of lintegral_mconv), lintegral_const, Measure.dirac_apply.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.additive_convolution_powers_mass
    (κ : Measure ℝ) [SFinite κ]
    (m : ℕ → Measure ℝ)
    (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n)) :
    ∀ n : ℕ, m n Set.univ = (κ Set.univ) ^ n := by sorry
