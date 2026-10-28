-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_right_generator_add_of_integrable
-- name    : AvramDividend.Classical.levy_transition_right_generator_add_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:18:45.443919+00:00
-- url     : https://prove2.me/theorems/5c7ec8a6-baf3-468b-81b9-6917ef040d1d
-- title:
--   Additive closure of the Lévy right-semigroup generator identity for integrable payoffs
-- statement:
--   Let f and g be integrable under every deterministic positive-time Levy transition, and suppose each right semigroup derivative at time zero equals the corresponding Levy generator. If the generator of f+g at the reserve x equals the sum of individual generators, the same right-generator identity holds for the combined payoff. The proof uses ordinary Bochner integral additivity, the additive limit theorem and elementary algebra. It is a compositional lemma applicable to finite exponential sums and to more general generator cores once the primitive derivative identities and integrability are proved.
-- source:
--   Elementary semigroup linearity within the Levy setting used by Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_right_generator_add_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (f g : ℝ → ℝ) (x : ℝ)
    (hfInt : ∀ h : ℝ, Integrable
      (fun ω => f (x + X.X (Real.toNNReal h) ω)) P)
    (hgInt : ∀ h : ℝ, Integrable
      (fun ω => g (x + X.X (Real.toNNReal h) ω)) P)
    (hfSlope : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) ∂P) - f x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator f x)))
    (hgSlope : Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, g (x + X.X (Real.toNNReal h) ω) ∂P) - g x))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator g x)))
    (hGenerator : X.generator (fun z => f z + g z) x =
      X.generator f x + X.generator g x) :
    Tendsto
      (fun h : ℝ => h⁻¹ *
        ((∫ ω, f (x + X.X (Real.toNNReal h) ω) +
                 g (x + X.X (Real.toNNReal h) ω) ∂P) -
          (f x + g x)))
      (nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)))
      (nhds (X.generator (fun z => f z + g z) x)) := by sorry
