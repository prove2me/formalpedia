-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_integral_tendsto_of_uniform_second_moment
-- name    : AvramDividend.Classical.nonnegative_integral_tendsto_of_uniform_second_moment
-- status  : Open
-- author  : @WillR
-- created : 2026-10-08T09:42:07.2348+00:00
-- url     : https://prove2.me/theorems/bef79c38-a4aa-42be-b897-fd1baeed7998
-- title:
--   Convergence of expectations under a uniform second-moment bound
-- statement:
--   On a probability space, let Y_n be nonnegative almost-everywhere and strongly measurable random variables converging pointwise almost surely to Z. If their second moments are integrable and uniformly bounded by C, then Z is integrable and E Y_n converges to E Z. The classical proof truncates at R>0, uses bounded dominated convergence for min(Y_n,R), and bounds every discarded tail by E Y_n²/R≤C/R using the quadratic pointwise inequality. Passing R→∞ establishes uniform integrability and convergence of expectations. This exact lemma will justify passage from the accepted finite-valued Lévy stopping-time moment identities to the bounded-stopping-time moment identity after right-continuous path convergence.
-- source:
--   Uniform integrability via second moments (Vitali convergence), Mathlib.MeasureTheory.Function.UniformIntegrable, pinned revision 0df444a360eaa60ab8c11dca51a86af692955474; Avram et al (2007), first-passage strong-Markov reasoning.

import Mathlib
open MeasureTheory Filter Topology

theorem AvramDividend.Classical.nonnegative_integral_tendsto_of_uniform_second_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hY0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ Y n ω)
    (hZ : AEStronglyMeasurable Z P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun n => Y n ω) atTop (𝓝 (Z ω)))
    (C : ℝ) (hC : 0 ≤ C)
    (hY2 : ∀ n, Integrable (fun ω => (Y n ω) ^ 2) P ∧
      ∫ ω, (Y n ω) ^ 2 ∂P ≤ C) :
    Integrable Z P ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂P) atTop
        (𝓝 (∫ ω, Z ω ∂P)) := by sorry
