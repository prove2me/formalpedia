-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_integrable_adapted_reserve_lipschitz
-- name    : AvramDividend.Classical.levy_increment_condExp_integrable_adapted_reserve_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:57:34.54744+00:00
-- url     : https://prove2.me/theorems/06df99a9-8ded-4440-9721-3829f15f2067
-- title:
--   Conditional Lévy Markov identity for an integrable adapted random reserve and a Lipschitz payoff
-- statement:
--   Let Z be integrable and adapted at time s for a spectrally negative Lévy process. Let f be a Lipschitz payoff with integrable deterministic shifted transitions, and assume only integrability of the actual shifted payoff at Z and at the canonical simple-function approximants. Then the conditional expectation of f(Z+X_t-X_s) given F_s equals the deterministic Lévy transition expectation starting at Z. Construct the canonical finite-valued adapted approximations via Mathlib SimpleFunc.approxOn. Their ordinary weighted L1 errors tend to zero, the approximating reserves are integrable, and the differences of random-reserve transition integrals are integrable by Lipschitz domination. Apply the general-reserve Markov theorem with automatic measurability. This removes explicit strong-measurability, approximation-limit, and transition-difference assumptions. The remaining payoff integrability could subsequently be derived from integrable Lévy increments, and this theorem does not establish stopped HJB verification.
-- source:
--   Accepted adaptedness, weighted L1, and Lipschitz Markov bounds; pending Prove2Me child proofs for strongly measurable transition and integrable transition differences. Dependency-gated until all are Proved.

import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_preserves_adaptedness
import Theorems.Thm_AvramDividend_Classical_simple_reserve_approxOn_weighted_real_L1
import Theorems.Thm_AvramDividend_Classical_levy_transition_random_reserve_integrable_difference_of_lipschitz
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_general_reserve_lipschitz_measurable

open Filter MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_integrable_adapted_reserve_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (f : ℝ → ℝ) (hf : Measurable f) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable
      (fun η => f (x + X.X (t - s) η)) P)
    (Z : Ω → ℝ)
    (hZ : Measurable[𝓕 s] Z) (hZm : Measurable Z)
    (hZI : Integrable Z P)
    (hZPay : Integrable
      (fun ω => f (Z ω + (X.X t ω - X.X s ω))) P)
    (hSPay : ∀ n : ℕ, Integrable (fun ω =>
      f ((SimpleFunc.approxOn Z hZm (Set.range Z ∪ {0}) 0
        (by simp) n) ω + (X.X t ω - X.X s ω))) P) :
    P[(fun η => f (Z η + (X.X t η - X.X s η))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ η, f (Z ω + X.X (t - s) η) ∂P) := by sorry
