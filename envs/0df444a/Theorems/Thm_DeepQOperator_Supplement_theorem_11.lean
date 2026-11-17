-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_11
-- name    : DeepQOperator.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:45:20.193039+00:00
-- url     : https://prove2.me/theorems/574fc5ee-6755-4720-9dd5-b4b21bad4680
-- title:
--   Theorem 11, p.34 — two adaptive raw queries cost at least $c_{\mathrm{raw}}\gamma$ on the envelope family
-- statement:
--   There is an absolute constant $c_{\mathrm{raw}}>0$ such that, for every $m\ge2$ and every $\gamma>0$, every randomized adaptive raw algorithm making at most two queries on every path satisfies, on the envelope family (13)–(14),
--   $$
--   \sup_{\theta\in[0,m+1]\times[0,1]^m}\mathbb{E}_\omega\,\ell\big(A(\theta;\omega),\theta\big)\ \ge\ c_{\mathrm{raw}}\gamma. \tag{62}
--   $$
--   Consequently, the exact adaptive raw-query complexity of this family is three. The same two-query lower bound holds under any additional quantization of the raw replies. Strict positive response mixing with weight $0<\lambda<1$ multiplies the lower bound by $1-\lambda$.
--
--   This is the raw-dictionary counterpart of Theorem 5, without an explicit constant.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: after any quantization of the replies → the algorithm observes $q(\text{reply})$ for an arbitrary jointly measurable real-valued observation map $q$ (seed and history dependent); reason: every standard Borel alphabet embeds measurably into $\mathbb{R}$
--   - reading: common positive response mixing multiplies the bound by $1-\lambda$ → for every $\lambda\in(0,1)$ the mixed family, built from the mixed Bellman scores (1), has worst regret at least $(1-\lambda)$ times the constant, for quantized algorithms as well; reason: mixing multiplies every loss by $1-\lambda$ and leaves the observations unchanged (p.10), so the scaled bound holds for every algorithm the unmixed bound covers
--   - encoding: there is an absolute constant $c_{\mathrm{raw}}>0$ → $\exists c>0$ chosen before $m$, $\gamma$, $\lambda$ and the algorithm; reason: the constant is absolute
--   - reading: exact adaptive raw-query complexity is three → a deterministic three-query raw algorithm with zero worst regret, together with (62); reason: exact complexity is two-sided
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 11 and eq. (62), p.34 (PDF p.37); proof in Appendix I, pp.34–36

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Envelope

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 11 (Sharp adaptive raw-query complexity)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy
Adaptive Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256
9f8f3285…), Theorem 11, p.34, PDF p.37; proved in Appendix I, pp.34–36).

There is an absolute constant `c_raw > 0` such that, for every `m ≥ 2` and `γ > 0`, every randomized
adaptive raw algorithm making at most two queries on every path has
`sup_{θ ∈ [0,m+1]×[0,1]^m} E_ω ℓ(A(θ; ω), θ) ≥ c_raw γ` (62) on the envelope family. Consequently the
exact adaptive raw-query complexity is three. The same two-query lower bound holds under any
additional quantization of the raw replies, and strict positive response mixing with weight
`λ ∈ (0,1)` multiplies it by `1 - λ`.

**Formalization Note.** `c_raw` is chosen before `m`, `γ`, the algorithm and `λ`. Algorithms are
measurable `AdaptiveAlg (EnvCoord m) Ω` on a standard Borel probability seed space whose every asked
query lies in `envDictionary m`, run with fuel `2`; "quantization" is an arbitrary jointly measurable
observation map (`IsExact` is the unquantized model). Three raw queries are attained by a
deterministic algorithm (`Unit` seed). The mixed family uses the mixed Bellman scores. -/
theorem theorem_11 :
    ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ →
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (EnvCoord m) Ω),
        A.IsExact → A.IsRaw (envDictionary m) → A.IsMeasurable →
        ENNReal.ofReal (c * γ) ≤ algRegret (envBox m) (envLoss m γ 0) μ A 2) ∧
      (∃ A : AdaptiveAlg (EnvCoord m) Unit, A.IsExact ∧ A.IsRaw (envDictionary m) ∧
        A.IsMeasurable ∧ algRegret (envBox m) (envLoss m γ 0) (Measure.dirac ()) A 3 = 0) ∧
      (∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (EnvCoord m) Ω),
        A.IsRaw (envDictionary m) → A.IsMeasurable →
        ENNReal.ofReal (c * γ) ≤ algRegret (envBox m) (envLoss m γ 0) μ A 2) ∧
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (A : AdaptiveAlg (EnvCoord m) Ω),
          A.IsRaw (envDictionary m) → A.IsMeasurable →
          ENNReal.ofReal ((1 - lam) * (c * γ)) ≤ algRegret (envBox m) (envLoss m γ lam) μ A 2) := by sorry

end DeepQOperator.Supplement
