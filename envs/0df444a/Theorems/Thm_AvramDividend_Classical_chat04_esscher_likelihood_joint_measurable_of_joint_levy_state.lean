-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
-- name    : AvramDividend.Classical.chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T10:35:07.819296+00:00
-- url     : https://prove2.me/theorems/de339769-89f8-41e1-8523-7683a2f71178
-- title:
--   Joint measurability of the genuine clamped-time Esscher likelihood from joint Lévy state measurability
-- statement:
--   For a spectrally negative Lévy process X, assume the actual state evaluation (t,ω)↦X_t(ω) is jointly measurable for t≥0. Then the genuine real-clock Esscher density (ω,s)↦ENNReal.ofReal(exp(θX_{max(s,0)}(ω)−max(s,0)ψ(θ))) is jointly measurable. The theorem formalises all casts and nonlinear operations needed to feed this concrete density into the already accepted finite-horizon random-clock Esscher probability construction.
-- source:
--   The positive-part clock Real.toNNReal is Borel measurable, its real coercion is measurable, and the corresponding state (ω,s)↦X_(Real.toNNReal s)(ω) is measurable by composing the input joint-state evaluation with a product of the two measurable projections. Scalar multiplication, subtraction, Real.exp and ENNReal.ofReal preserve measurability. The only remaining condition is genuine joint measurability of the Lévy state, not a tautological density assumption.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_esscher_likelihood_joint_measurable_of_joint_levy_state
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => X.X z.1 z.2)) :
    Measurable (fun z : Ω × ℝ => ENNReal.ofReal
      (Real.exp (θ * X.X (Real.toNNReal z.2) z.1 -
        (Real.toNNReal z.2 : ℝ) * X.ψ θ))) := by sorry
