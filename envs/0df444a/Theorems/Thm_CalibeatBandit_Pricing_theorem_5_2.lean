-- Prove2me | Theorems.Thm_CalibeatBandit_Pricing_theorem_5_2
-- name    : CalibeatBandit.Pricing.theorem_5_2
-- status  : Proved
-- author  : @jasonhartline
-- created : 2026-11-15T14:13:48.746831+00:00
-- url     : https://prove2.me/theorems/d699d004-8d19-431b-9fe7-8b3d0d3c8796
-- title:
--   Theorem 5.2 — Continuous pricing lower bound
-- statement:
--   There are absolute constants $c>0$ and $T_0$ such that for every $T\ge T_0$ there is a sparsity $K>0$ with the following property. For every measurable randomized bandit pricing policy, there are a deterministic oblivious sequence of nonincreasing demands and a deterministic recommendation sequence using at most $K$ prices. On this instance both expected swap regret and expected recommendation reward loss are at least $c(T^{3/4}+K^{1/3}T^{2/3})/(\log T)^6$. The pricing rule may depend on the complete fixed recommendation sequence. The proof chooses one possible recommendation price for each leaf of the hard instance, as in the manuscript.
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice, STOC 2027 submission 1457, Theorem 5.2 — Continuous pricing lower bound

import Definitions.Def_CalibeatBandit_lower_bound_models

open CalibeatBandit.Pricing MeasureTheory Set

theorem CalibeatBandit.Pricing.theorem_5_2 :
    ∃ c : ℝ, 0 < c ∧ ∃ T₀ : ℕ, ∀ T : ℕ, T₀ ≤ T →
      ∃ K : ℕ, 0 < K ∧ ∀ {S : Type*} [MeasurableSpace S] (P : Measure S)
        [IsProbabilityMeasure P] (rule : (ℕ → Price) → S → PricingRule),
        (∀ a t, Measurable (fun p : S × (Fin t → Price × ℝ) => rule a p.1 t p.2)) →
        ∃ (d : ℕ → Demand) (recommendationPrice : Fin K → Price) (label : ℕ → Fin K),
          let recommendations := recommendationPrice ∘ label
          let posted (s : S) (t : ℕ) :=
            rule recommendations s t (pricingHistory (rule recommendations s) (fun i => revenue zeroPrice (d i)) t)
          let rate := c * ((T : ℝ) ^ (3 / 4 : ℝ) + (K : ℝ) ^ (1 / 3 : ℝ) * (T : ℝ) ^ (2 / 3 : ℝ)) /
            Real.log T ^ 6
          (rate ≤ ∫ s, benchmark T zeroPrice d (posted s) (posted s) ∂P) ∧
            (rate ≤ ∫ s, benchmark T zeroPrice d recommendations (posted s) ∂P) := by sorry
