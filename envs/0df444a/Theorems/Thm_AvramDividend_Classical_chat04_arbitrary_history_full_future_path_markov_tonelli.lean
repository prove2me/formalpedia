-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_arbitrary_history_full_future_path_markov_tonelli
-- name    : AvramDividend.Classical.chat04_arbitrary_history_full_future_path_markov_tonelli
-- status  : Open
-- author  : @WillR
-- created : 2026-10-21T08:04:11.864498+00:00
-- url     : https://prove2.me/theorems/2ceb6bc9-a37a-4173-aca1-e365326146a8
-- title:
--   Full future-path Markov–Tonelli identity for arbitrary historical state and nonnegative path-dependent payoff
-- statement:
--   For a spectrally negative Lévy process X at deterministic time s, let H:Ω→E be any F_s-measurable historical state or full record of past survival and reserve. Assume that the jointly observed finite vector of all shifted future increments (X_(s+t)−X_s) at each finite set of times t is independent of H. Then for EVERY measurable nonnegative extended-real payoff f depending jointly on H and the ENTIRE future shifted path, its expectation under the original process equals the double integral of f against the product of the law of H and the law of the whole shifted future process. This full-path Markov–Tonelli identity is exact without moment or integrability hypotheses: f may be an indicator of continuous-time survival multiplied by a discounted nonnegative terminal reward, provided it is product-measurable. It follows from the officially ACCEPTED theorem chat04_full_shifted_future_path_indep_of_all_finite_cylinders UUID 7b8aa9ab-9dc6-4b9a-a595-32d384e805ca, together with the pinned Mathlib independence-to-product-law, lintegral_map and lintegral_prod identities. The finite-cylinder independence premise is explicit and still needs a uniform derivation from the original Lévy axiom; no killed q-harmonicity is smuggled into the result.
-- source:
--   ACCEPTED full process cylinder-to-path independence UUID 7b8aa9ab-9dc6-4b9a-a595-32d384e805ca; pinned Mathlib MeasureTheory.lintegral_map, lintegral_prod and ProbabilityTheory.IndepFun.map_prod_eq_prod_map_map.

import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Independence.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_full_shifted_future_path_indep_of_all_finite_cylinders

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_arbitrary_history_full_future_path_markov_tonelli
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    {E : Type*} [MeasurableSpace E]
    (X : SpectrallyNegativeLevy P 𝓕)
    (s : ℝ≥0)
    (H : Ω → E) (hH : Measurable[𝓕 s] H)
    (hFinite : ∀ I : Finset ℝ≥0,
      IndepFun
        (fun ω (i : I) => X.X (s + (i : ℝ≥0)) ω - X.X s ω)
        H P)
    (f : E × (ℝ≥0 → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f (H ω,
        (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) ∂P) =
    ∫⁻ h, ∫⁻ y, f (h, y)
      ∂(Measure.map
        (fun ω => (fun t : ℝ≥0 => X.X (s + t) ω - X.X s ω)) P)
      ∂(Measure.map H P) := by sorry
