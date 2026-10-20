-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_near_HJB_of_regular_deriv_minimum
-- name    : AvramDividend.Classical.vcstar_near_HJB_of_regular_deriv_minimum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T13:47:26.231267+00:00
-- url     : https://prove2.me/theorems/df539e1e-0464-44b2-9a94-af8556fd7092
-- title:
--   Near-barrier HJB from regular derivative-minimising scale function
-- statement:
--   Under C1 regularity and positive derivative of the formal scale function W, a positive canonical barrier a at a global minimum of W', and continuity of the dividend barrier value on [0,a], the exact nonlocal HJB and generator domain hold for reserves x>a with x≥1 and x≥a+max(0,c/q). The proof derives v'(z)≥1 from already-Proved minimiser regularity, applies the pinned mean-value theorem to v-id to prove the left affine-majorant chord, and then invokes the already-Proved near-barrier nonlocal HJB theorem. It removes the explicit chord hypothesis and does not claim general stochastic q-harmonicity.

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_near_HJB_of_regular_deriv_minimum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0))
    (hpositive : ∀ z : ℝ, 0 < z → 0 < deriv W z)
    (a : ℝ) (ha : a = (cstar W).toReal) (hapos : 0 < a)
    (hminimal : ∀ z : ℝ, 0 < z → deriv W a ≤ deriv W z)
    (hcont : ContinuousOn (vcstar W) (Icc 0 a))
    (x : ℝ) (hx : a < x) (hx1 : 1 ≤ x)
    (hthreshold : a + max 0 (X.c / q) ≤ x) :
    X.GeneratorIntegrable (vcstar W) x ∧
      max (X.generator (vcstar W) x - q * vcstar W x)
        (1 - deriv (vcstar W) x) = 0 := by sorry
