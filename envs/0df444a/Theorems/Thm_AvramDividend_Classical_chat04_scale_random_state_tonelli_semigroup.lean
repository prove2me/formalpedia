-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_random_state_tonelli_semigroup
-- name    : AvramDividend.Classical.chat04_scale_random_state_tonelli_semigroup
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:27:50.357769+00:00
-- url     : https://prove2.me/theorems/5fbd9ecf-4d28-433d-9e0b-a59843042b4a
-- title:
--   Random-state Lévy q-scale semigroup expectation as a product-measure integral
-- statement:
--   For every spectrally negative Lévy process, its q-scale function W, deterministic x and 0≤s≤t, the nonnegative expectation of W(x+X_t) equals the double Lebesgue integral of W(x+u+v) under the product of the law of the random current state X_s and the law of X_(t−s). The identity allows extended nonnegative integrals and does not assume integrability. Prove the exact stationary independent-increment product joint law from the actual filtration axioms, then apply pinned Mathlib lintegral_map and Tonelli's lintegral_prod. It is a genuine random-state semigroup identity, but remains unrestricted: no killing below zero or stopped scale q-harmonicity is assumed.
-- source:
--   Original SpectrallyNegativeLevy adapted/independent/stationary increments, Proved full-line q-scale Borel measurability UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab, pinned Mathlib IndepFun.map_prod_eq_prod_map_map, IdentDistrib.map_eq, lintegral_map, lintegral_prod.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_scale_random_state_tonelli_semigroup
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t : ℝ≥0) (hst : s ≤ t) (x : ℝ) :
    (∫⁻ ω, ENNReal.ofReal (W (x + X.X t ω)) ∂P) =
      ∫⁻ u, ∫⁻ v, ENNReal.ofReal (W (x + u + v))
          ∂(Measure.map (X.X (t - s)) P)
          ∂(Measure.map (X.X s) P) := by sorry
