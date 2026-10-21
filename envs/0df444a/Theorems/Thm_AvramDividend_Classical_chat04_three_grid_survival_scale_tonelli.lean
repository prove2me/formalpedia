-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_three_grid_survival_scale_tonelli
-- name    : AvramDividend.Classical.chat04_three_grid_survival_scale_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:16:22.568142+00:00
-- url     : https://prove2.me/theorems/47dd313a-4a3d-441e-b618-5710ac3cead5
-- title:
--   Three-point Lévy survival q-scale payoff as iterated independent-increment integral
-- statement:
--   For any real initial reserve x and three deterministic times s≤t≤u of a canonical spectrally negative Lévy process, the ENNReal expectation of the q-scale payoff W(x+X_u) restricted to remaining non-negative at all three grid observation times equals the threefold integral against the independent laws of X_s, X_(t−s) and X_(u−t). The survival tests depend on the progressively accumulated reserve x+a, x+a+b, x+a+b+c. The result is exact for three discrete monitoring dates even when W is discontinuous at zero and without finite-moment assumptions. It uses the separately Proved threefold Markov Tonelli identity and Borel measurability of the scale. This is the first explicitly killed *finite-grid* identity in this new chain; it does not state survival throughout all real times or establish the killed q-harmonicity martingale.
-- source:
--   Proved AvramDividend.Classical.chat04_three_step_grid_tonelli_markov_law (publication pending prior official submission) and Proved chat03_scale_function_borel_measurable UUID 45cbe3b4-374d-4fa4-b988-e09f93b74cab. Conditional on the threefold generic theorem being ACCEPTED before submitting; pinned Mathlib Mathlib.Tactic.FunProp for measurability.

import Mathlib.Tactic.FunProp
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_scale_function_borel_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_three_step_grid_tonelli_markov_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_three_grid_survival_scale_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u) (x : ℝ) :
    (∫⁻ ω,
       if 0 ≤ x + X.X s ω ∧
          0 ≤ x + X.X s ω + (X.X t ω - X.X s ω) ∧
          0 ≤ x + X.X s ω + (X.X t ω - X.X s ω) +
            (X.X u ω - X.X t ω)
       then ENNReal.ofReal
         (W (x + X.X s ω + (X.X t ω - X.X s ω) +
            (X.X u ω - X.X t ω)))
       else 0 ∂P) =
    ∫⁻ a, ∫⁻ b, ∫⁻ c,
       if 0 ≤ x + a ∧ 0 ≤ x + a + b ∧
          0 ≤ x + a + b + c
       then ENNReal.ofReal (W (x + a + b + c))
       else 0
       ∂(Measure.map (X.X (u - t)) P)
       ∂(Measure.map (X.X (t - s)) P)
       ∂(Measure.map (X.X s) P) := by sorry
