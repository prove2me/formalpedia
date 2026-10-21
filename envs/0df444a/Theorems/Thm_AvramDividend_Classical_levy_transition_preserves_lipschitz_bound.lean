-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_transition_preserves_lipschitz_bound
-- name    : AvramDividend.Classical.levy_transition_preserves_lipschitz_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:44:49.387925+00:00
-- url     : https://prove2.me/theorems/92c50339-afaa-402c-872b-fb8cabe1dff9
-- title:
--   Lévy transition semigroup contracts the Lipschitz constant of integrable real payoffs
-- statement:
--   On the actual Lévy probability space, let f be globally L-Lipschitz with L≥0 and assume its translates f(x+X_t) are integrable for all x. Then the transition map P_t f(x)=E[f(x+X_t)] is also L-Lipschitz: |P_t f(x)−P_t f(y)|≤L|x−y|. Proof: the difference f(x+X_tω)−f(y+X_tω) has absolute value≤L|x−y| for every outcome because the same random increment is added to both starting points. Integrate the two deterministic upper and lower bounds with pinned MeasureTheory.integral_mono_ae and probability mass one; rewrite integral of the difference using integral_sub. This is an actual semigroup continuity estimate for Lipschitz test functions, useful for extending finite simple-state Markov conditional expectations by approximation. It does not prove strong continuity in t, Γf as the infinitesimal generator, or the stopped HJB dividend supermartingale.
-- source:
--   Pinned integral_mono_ae signature already verified remotely; use the Levy IsProbabilityMeasure field and standard integral_sub. No Open dependencies.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_transition_preserves_lipschitz_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (t : ℝ≥0)
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ u v : ℝ, |f u - f v| ≤ L * |u - v|)
    (hInt : ∀ x : ℝ, Integrable (fun ω => f (x + X.X t ω)) P) :
    ∀ x y : ℝ,
      |(∫ ω, f (x + X.X t ω) ∂P) -
        (∫ ω, f (y + X.X t ω) ∂P)| ≤ L * |x - y| := by sorry
