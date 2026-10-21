-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_valued_reserve
-- name    : AvramDividend.Classical.levy_increment_condExp_finite_valued_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:56:02.79201+00:00
-- url     : https://prove2.me/theorems/cbd1ef08-c269-4698-9126-2f4a4877d524
-- title:
--   Full conditional Markov identity for an arbitrary finite-valued past-measurable Lévy starting reserve
-- statement:
--   Let X be the actual Lévy process, s≤t, and p:Ω→ι take values in any finite type ι. Assume every fibre {ω:pω=i} is measurable in F_s; let x_i be the reserve level associated with state i. For Borel measurable payoff f with integrability of every deterministic shifted payoff f(x_i+X_(t−s)), prove E[f(x_(pω)+X_t−X_s)|F_s](ω)=E[f(x_(pω)+X_(t−s))] almost everywhere. This is the exact Markov property for a finite-valued random initial reserve, rather than just a linear identity for indicator-weighted payoffs. Partition Ω into the measurable disjoint fibre events of p, apply the previously Proved finite simple-state conditional Markov identity, and identify each finite sum with its unique surviving state by Finset.sum_ite_eq. The theorem is dependency-gated on the remote acceptance of finite_simple_state. It is a step toward the general random-state Markov property, not a claim that the semigroup generator equals Γf or that the stopped stochastic HJB budget is proved.
-- source:
--   Uses already published finite simple-state theorem 0de453cb-633f-4cc1-9a60-4bca488e5859 only after an authoritative Proved verdict; finite partition identity by exact indicator summation.

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_increment_condExp_finite_simple_state

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_increment_condExp_finite_valued_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    {ι : Type*} [Fintype ι]
    (p : Ω → ι)
    (hp : ∀ i, MeasurableSet[𝓕 s] {ω : Ω | p ω = i})
    (x : ι → ℝ) (f : ℝ → ℝ) (hf : Measurable f)
    (hI : ∀ i, Integrable (fun ω => f (x i + X.X (t - s) ω)) P) :
    P[(fun ω => f (x (p ω) + (X.X t ω - X.X s ω))) | 𝓕 s] =ᵐ[P]
      (fun ω => ∫ ω', f (x (p ω) + X.X (t - s) ω') ∂P) := by sorry
