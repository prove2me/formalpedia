-- Prove2me | Theorems.Thm_CorrelatedRounding_theorem_1
-- name    : CorrelatedRounding.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:37:25.591352+00:00
-- url     : https://prove2.me/theorems/61ba9ba4-6281-4f25-8ae8-6ab3c87d78d1
-- title:
--   Theorem 1 — Algorithm 1 is a $(1+\ln q)$-competitive rounding scheme with runtime $O(qK)$
-- statement:
--   There is a constant $C$ such that for all $q\ge1$, all $K$ and every instance $u$:
--
--   1. for every real vector $E$, the program of Algorithm 1 uses at most $C\,q\,K$ ticks, assigns every item an FC, and its assignment is a valid output of Algorithm 1;
--   2. a draw of Algorithm 1 exists on some probability space;
--   3. for every draw $(E_k)_k$ on a probability space and every $Z$ valued almost surely in the arg min, the marginals are exact and the competitive bound holds:
--   $$\Pr[Z_i=k]=u_{ki}\quad\text{for all } i,k,\qquad \Pr\Big[\bigcup_{i=1}^q (Z_i=k)\Big]\le(1+\ln q)\,y_k\quad\text{for all } k.$$
--
--   Here $y_k=\max_i u_{ki}$ is the unavoidable lower bound on the probability of using FC $k$. Algorithm 1 draws one independent exponential clock per FC with rate $y_k$ and sends item $i$ to the FC minimizing $(y_k/u_{ki})E_k$. The theorem improves the linear guarantee of Jasin and Sinha (2015) to a logarithmic one.
--
--   **Formalization Note.** Running time is counted in the published real-RAM tick model. The tie-break $Z$ carries no measurability hypothesis, and the measure of a possibly non-measurable set is outer measure.
--
--   Differences from the source:
--   - reading: "runtime O(qK)", with no machine model named → ∃ C : ℕ chosen before every input with ticks of the explicit program alg1Prog at most C·q·K; one tick per read of u, per read of a draw, per real operation and per loop iteration; reason: the inputs are real numbers, so the published real-RAM tick model is the natural reading; computing y from u is charged
--   - reading: "Break ties arbitrarily" → every Z valued almost surely in the arg min, with no measurability and no fixed rule; μ of a possibly non-measurable set is outer measure; reason: the strongest reading; it covers every tie rule, because ties between finite clocks are null events
--   - generalization: "Assume without loss that y_k > 0 for all k" (p.9) → an FC with y_k = 0 is allowed, and its entry of the draw is unconstrained; reason: such an FC has clock ∞ at every item; the page's instances, all y_k > 0, are a special case
--   - encoding: the scheme's draws are taken for granted → clause 2, a draw exists on some probability space; reason: it rules out a vacuous clause 3, in particular at y_k = 0
--   - encoding: items i = 1,…,q, with q left implicit → the hypothesis 1 ≤ q; reason: the K draws cost K > 0 = C·0·K, so the bound needs q ≥ 1; K ≥ 1 then follows from the instance
--   - encoding: items i = 1,…,q and FCs k = 1,…,K → Fin q and Fin K, both 0-based; reason: Lean convention; same instances
--   - encoding: (y_k/u_ki) E_k = ∞ if u_ki = 0 (p.9) → the clock is ⊤ : EReal at u_ki = 0; reason: the page's convention; only ≤ is applied to clocks
-- source:
--   Ma, Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders, arXiv:2207.04774v4, Theorem 1, p.11

import Mathlib
import Definitions.Def_CorrelatedRounding_IsInstance
import Definitions.Def_CorrelatedRounding_y
import Definitions.Def_CorrelatedRounding_clock
import Definitions.Def_CorrelatedRounding_IsAlg1Output
import Definitions.Def_CorrelatedRounding_IsAlg1Draw
import Definitions.Def_CorrelatedRounding_alg1Prog

open MeasureTheory ProbabilityTheory

namespace CorrelatedRounding

/-- **Theorem 1.** W. Ma, *Order-optimal Correlated Rounding for Fulfilling Multi-item E-commerce Orders*, arXiv:2207.04774v4, p.11:
"Algorithm 1 is a (1 + ln(q))-competitive rounding scheme with runtime O(qK)."

There is a constant `C`, chosen before every input, such that for every `q ≥ 1`, `K` and instance `u`:
1. for every real vector `E`, the program `alg1Prog u E` run from `0` uses at most `C * q * K` ticks, returns
   `some` at every item, and its assignment is a valid output of Algorithm 1;
2. the scheme exists: some probability space carries a draw of Algorithm 1;
3. for every probability space, every draw `E`, and every `Z` almost surely in the arg min, the marginals
   are exact, `Pr[Z_i = k] = u_ki` (a rounding scheme, Definition 1, p.9), and each FC is used with probability
   at most `(1 + ln q) y_k` (`(1 + ln q)`-competitive, Definition 1, p.9).

**Formalization Note.** Clause 3 covers every tie-break, with no measurability of `Z`; `μ` of a possibly
non-measurable set is outer measure. It therefore applies to the program's first-minimum rule through clause 1.
Definition 1 assumes `y_k > 0` "without loss"; here `y_k = 0` is allowed (see `IsAlg1Draw`), and then the FC is
never used. "Runtime" is the real-RAM reading of `alg1Prog`; the program takes the realized draws as input and
charges one tick per draw. -/
theorem theorem_1 :
    ∃ C : ℕ, ∀ (q K : ℕ), 1 ≤ q → ∀ (u : Fin K → Fin q → ℝ), IsInstance u →
      (∀ E : Fin K → ℝ,
        ((alg1Prog u E).run 0).2 ≤ C * q * K ∧
        ∃ z : Fin q → Fin K, (∀ i, ((alg1Prog u E).run 0).1 i = some (z i)) ∧ IsAlg1Output u E z) ∧
      (∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (_ : IsProbabilityMeasure μ)
        (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E) ∧
      (∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (E : Fin K → Ω → ℝ), IsAlg1Draw u μ E →
        ∀ Z : Ω → Fin q → Fin K, (∀ᵐ ω ∂μ, IsAlg1Output u (fun k => E k ω) (Z ω)) →
          (∀ i k, μ {ω | Z ω i = k} = ENNReal.ofReal (u k i)) ∧
          ∀ k, μ (⋃ i, {ω | Z ω i = k}) ≤ ENNReal.ofReal ((1 + Real.log q) * y u k)) := by sorry

end CorrelatedRounding
