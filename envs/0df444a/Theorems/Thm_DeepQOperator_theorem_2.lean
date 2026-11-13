-- Prove2me | Theorems.Thm_DeepQOperator_theorem_2
-- name    : DeepQOperator.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:08:42.804364+00:00
-- url     : https://prove2.me/theorems/83c5b918-e30d-4a5d-861b-ecdc65df6a93
-- title:
--   Theorem 2: $\Theta(m)$ fixed versus $\Theta(\log m)$ adaptive reply bits on the bounded convex box
-- statement:
--   Consider the three-row Bellman family (6) on the full convex box $P_{cb}=[-1,1]^n\times[0,1]^m$, $m\ge2$, $0<\gamma<1$, in the separately quantized scalar-reply model: each reply is a symbol of a charged length, its quantizer sees only its own affine scalar, the shared seed and earlier symbols, and the total length is at most $B$ on every input and random path.
--
--   1. For every integer hard reply budget $B\ge0$, every fixed protocol with arbitrary affine queries, and every adaptive one, has worst-input expected regret
--   $$\mathfrak h^{\mathrm{fixed,aff,bit}}_B\ \ge\ \frac{\gamma(m-B)_+}{256\pi^2m},\qquad \mathfrak h^{\mathrm{adaptive,aff,bit}}_B\ \ge\ \frac{\gamma(m+1-2^B)_+}{256\pi^2m}.\tag{7}$$
--   2. For every $\varepsilon>0$, with
--   $$\delta=\min\{1/2,16\varepsilon/\gamma\},\qquad R=2\lceil\log_2(m/\delta)\rceil+1,\qquad v=\max\{1,\lceil\log_2(8\gamma/\varepsilon)\rceil\},\tag{8}$$
--   there is an at-most-two-stage randomized adaptive raw protocol with worst-input expected regret at most $\varepsilon$ and hard reply-bit budget
--   $$\min\{2mv,\ 5120R+2\min(m,64)v\},\tag{9}$$
--   all of whose queried sites belong to the raw dictionary and whose quantizers are the uniform quantizers (41).
--   3. Every raw site has affine coefficient $\ell_1$ norm at most one and range in $[-1,1]$ on $P_{cb}$.
--   4. For each fixed $0<\varepsilon/\gamma\le1/(512\pi^2)$, the optimal fixed reply cost is $\Theta(m)$ and the optimal adaptive cost is $\Theta(\log m)$, for both the raw and the arbitrary-affine scalar-reply models: there are constants $0<c\le C$ depending only on $\varepsilon/\gamma$ such that a fixed raw protocol with budget at most $Cm$ and an adaptive raw protocol with budget at most $C\log m$ attain regret $\varepsilon$, and every fixed (resp. adaptive) affine protocol attaining regret $\varepsilon$ has budget at least $cm$ (resp. $c\log m$).
--
--   The theorem separates fixed from adaptive acquisition of a shared critic at a fixed tolerance, with bounded raw values and slopes, against lower bounds that allow arbitrary measurable scalar quantizers and decoders.
--
--   **Formalization Note** Protocols, budgets and regret are those of `Def_DeepQOperator_ReplyProtocol`; seed spaces are standard Borel probability spaces and protocols are measurable. Raw protocols are affine protocols, so the affine lower bounds cover the raw class and the raw upper bounds cover the affine class.
--
--   Differences from the source:
--   - encoding: a reply of length d ≥ 0 bits in an alphabet of size at most 2^d → every asked field has length ≥ 1 and its symbol lies in {0, …, 2^d − 1}; reason: App. A: "A zero-bit reply is constant and can be removed"; an alphabet of size at most 2^d is a subset of {0, …, 2^d − 1}
--   - reading: a fixed design "preselects its whole list of maps, quantizers and lengths from the seed alone" → IsFixed: asking, maps and lengths depend on the history only through its length; the quantizer of a field may also read earlier symbols; reason: App. A lets every quantizer see earlier symbols; reading the preselected quantizer as a function of them gives the larger fixed class, hence the stronger lower bound (the constructed fixed protocol uses quantizers that do not read them)
--   - encoding: randomness on a standard Borel space → seed space Ω : Type with [StandardBorelSpace Ω] and a probability measure; the protocol is measurable in the seed, quantizers jointly measurable; reason: §5 p.8; every standard Borel space is Borel isomorphic to a Borel subset of ℝ, so Ω : Type omits none
--   - encoding: "the sum of lengths is at most B on every input and random path" → HardBudgetOn (Pcb m) B: for every θ ∈ P_cb, every seed ω and every number of steps, the charged lengths along the run total at most B; regret is computed from the run with fuel B; reason: same condition; with lengths ≥ 1 the run asks at most B fields
--   - encoding: 𝔥^{…}_B, the infimum over protocols of sup_θ E_ω ℓ → every protocol of the class satisfies bound ≤ ⨆_{θ ∈ P_cb} ∫⁻ ω, ofReal ℓ(A(θ;ω), θ) dμ; reason: an infimum is ≥ a bound iff every member is; the supremum need not be attained
--   - reading: "the optimal fixed reply cost is Θ(m) and the optimal adaptive cost is Θ(log m)" for each fixed ε/γ → ∀ κ ∈ (0, 1/(512π²)], ∃ c, C > 0, ∀ m ≥ 2, ∀ γ ∈ (0,1), with ε = κγ: a measurable raw protocol with the uniform quantizers (41) (fixed, resp. adaptive) with budget ≤ Cm (resp. ≤ C log m) and worst regret ≤ ε exists, and every affine protocol (fixed, resp. adaptive) with worst regret ≤ ε has budget ≥ cm (resp. ≥ c log m); reason: Θ of the optimal cost, with constants depending only on the fixed tolerance ratio; raw ⊂ affine gives both classes; avoids sInf of a possibly empty set of budgets
--   - generalization: "All queried sites belong to the original raw dictionary. Their affine coefficient ℓ1 norms are at most one and their ranges lie in [−1, 1]" → every site of the raw dictionary has ℓ1 norm ≤ 1 and range in [−1, 1] on P_cb, and the protocol is raw; reason: the queried sites are dictionary sites
--   - encoding: "randomized adaptive raw protocol" → a measurable ReplyProtocol on a standard Borel probability seed space with IsRaw; reason: an adaptive protocol is any protocol of the model
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), §3.1, Theorem 2, eqs. (7)–(9), p.4 (PDF pp.7–8)

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_Quantizer
import Definitions.Def_DeepQOperator_ReplyProtocol
import Definitions.Def_DeepQOperator_Sampling

open MeasureTheory

namespace DeepQOperator

/-- **Theorem 2 (Finite replies on the bounded convex box)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions*,
STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 2, p.4, PDF pp.7–8).

For the family (6) with `m ≥ 2` and `0 < γ < 1`, in the separately quantized scalar-reply model:
1. for every integer hard reply budget `B ≥ 0`, every fixed affine protocol has worst-input expected
   regret at least `γ(m - B)₊/(256π²m)` and every adaptive affine protocol at least
   `γ(m + 1 - 2^B)₊/(256π²m)` (7);
2. for every `ε > 0`, with `δ, R, v` of (8), there is an at-most-two-stage randomized adaptive raw
   protocol with worst-input expected regret at most `ε` and hard reply-bit budget
   `min{2mv, 5120R + 2min(m, 64)v}` (9), whose quantizers are the uniform quantizers (41);
3. every raw site has affine coefficient `ℓ₁` norm at most one and range in `[-1, 1]` on `P_cb`;
4. for each fixed `0 < ε/γ ≤ 1/(512π²)` the optimal fixed reply cost is `Θ(m)` and the optimal adaptive
   cost is `Θ(log m)`, for both the raw and the arbitrary-affine scalar-reply models.

**Formalization Note.** Protocols are `ReplyProtocol (Coord m) Ω` on a standard Borel probability
seed space `(Ω, μ)`: each field's quantizer sees only its own scalar, the seed and earlier symbols;
lengths are `≥ 1` (zero-bit fields removed); the budget is hard on every input of `P_cb` and every seed.
"Fixed" is `IsFixed`, "raw" is `IsRaw`, "uniform quantizers" is `UsesUniformQuantizers`. The worst
regret is the `⨆` of lower Lebesgue integrals `worstRegret`. Raw protocols are affine protocols, so
the affine lower bounds cover the raw class and the raw upper bounds cover the affine class. Clause 4
reads `Θ` with constants `c, C > 0` depending only on `κ = ε/γ`, chosen before `m` and `γ`; the cost is
the natural logarithm (any base changes only `c, C`). -/
theorem theorem_2 :
    (∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (P : ReplyProtocol (Coord m) Ω),
        P.IsMeasurable → P.IsFixed → P.HardBudgetOn (Pcb m) B →
        ENNReal.ofReal (γ * max 0 ((m : ℝ) - B) / (256 * Real.pi ^ 2 * m)) ≤
          worstRegret m γ μ P B) ∧
      (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (P : ReplyProtocol (Coord m) Ω),
        P.IsMeasurable → P.HardBudgetOn (Pcb m) B →
        ENNReal.ofReal (γ * max 0 ((m : ℝ) + 1 - 2 ^ B) / (256 * Real.pi ^ 2 * m)) ≤
          worstRegret m γ μ P B) ∧
      (∀ ε : ℝ, 0 < ε →
        ∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
          (_ : IsProbabilityMeasure μ) (P : ReplyProtocol (Coord m) Ω),
          IsRaw P ∧ P.IsAtMostTwoStage ∧ UsesUniformQuantizers P ∧ P.IsMeasurable ∧
          P.HardBudgetOn (Pcb m)
            (min (2 * m * vParam γ ε) (5120 * RParam m γ ε + 2 * min m 64 * vParam γ ε)) ∧
          worstRegret m γ μ P
            (min (2 * m * vParam γ ε) (5120 * RParam m γ ε + 2 * min m 64 * vParam γ ε)) ≤
            ENNReal.ofReal ε) ∧
      (∀ q ∈ rawDictionary m, ∑ c, |q.1 c| ≤ 1 ∧ ∀ θ ∈ Pcb m, affEval q θ ∈ Set.Icc (-1 : ℝ) 1)) ∧
    (∀ κ : ℝ, 0 < κ → κ ≤ 1 / (512 * Real.pi ^ 2) →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (P : ReplyProtocol (Coord m) Ω) (B : ℕ),
          IsRaw P ∧ P.IsFixed ∧ UsesUniformQuantizers P ∧ P.IsMeasurable ∧
          P.HardBudgetOn (Pcb m) B ∧ (B : ℝ) ≤ C * m ∧
          worstRegret m γ μ P B ≤ ENNReal.ofReal (κ * γ)) ∧
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (P : ReplyProtocol (Coord m) Ω),
          P.IsMeasurable → P.IsFixed → P.HardBudgetOn (Pcb m) B →
          worstRegret m γ μ P B ≤ ENNReal.ofReal (κ * γ) → c * m ≤ B) ∧
        (∃ (Ω : Type) (_ : MeasurableSpace Ω) (_ : StandardBorelSpace Ω) (μ : Measure Ω)
            (_ : IsProbabilityMeasure μ) (P : ReplyProtocol (Coord m) Ω) (B : ℕ),
          IsRaw P ∧ UsesUniformQuantizers P ∧ P.IsMeasurable ∧
          P.HardBudgetOn (Pcb m) B ∧ (B : ℝ) ≤ C * Real.log m ∧
          worstRegret m γ μ P B ≤ ENNReal.ofReal (κ * γ)) ∧
        (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
            [IsProbabilityMeasure μ] (P : ReplyProtocol (Coord m) Ω),
          P.IsMeasurable → P.HardBudgetOn (Pcb m) B →
          worstRegret m γ μ P B ≤ ENNReal.ofReal (κ * γ) → c * Real.log m ≤ B)) := by sorry

end DeepQOperator
