-- Prove2me | Theorems.Thm_BilateralProfitRegular_huber_factory
-- name    : BilateralProfitRegular.huber_factory
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:13.961689+00:00
-- url     : https://prove2.me/theorems/874c7ad9-0f52-4f23-9f61-383ece984b1b
-- title:
--   Bernoulli factory for $B_0\sim\mathrm{Ber}(P(z)/(20\widehat P(w)))$ with $O(1/\widehat P(w))$ expected rounds (cited from Huber 2016, Theorem 1)
-- statement:
--   This is the step of the proof of Lemma 6.5 that represents the reference probability by a bit $B_0\sim\mathrm{Ber}\big(P(z)/(20\widehat P(w))\big)$. It is cited from M. Huber, *Nearly optimal Bernoulli factories for linear functions* (Combin. Probab. Comput. 2016), Theorem 1, together with thinning when $20\widehat P(w)\ge1$.
--
--   There is a universal constant $C$ such that, for every multiplier $c>0$, there is a procedure with the following property. Given i.i.d. flips of a coin with unknown bias $p\in[0,1]$ satisfying $cp\le1/2$, the procedure:
--
--   1. stops almost surely;
--   2. outputs a bit equal to $1$ with probability exactly $cp$;
--   3. uses at most $C\max(1,c)$ coin flips in expectation.
--
--   In the paper $c=1/(20\widehat P(w))$ with $\widehat P(w)\in[\delta,1]$ and $p=P(z)$, so the cost is $O(1/\widehat P(w))$.
--
--   Differences from the source:
--   - generalization: multiplier $1/(20\widehat P(w))$ with $\widehat P(w)\in[\delta,1]$; cost $O(1/\widehat P(w))$ → every multiplier $c>0$; cost $C\max(1,c)$; reason: covers Huber's case $c>1$ and the thinning case $c\le1$; for $c\ge1/20$, $\max(1,c)\le20c$, which is the paper's $O(1/\widehat P(w))$
--   - encoding: a factory generating a bit from trade bits (coin flips) → a sampling procedure with the single query "flip", Bernoulli$(p)$ answers realized from uniforms; chosen before $p$; reason: the factory never sees $p$; same law of everything it observes
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Lemma 6.5, p.42 (PDF 44); cited: M. Huber, Nearly optimal Bernoulli factories for linear functions, Combin. Probab. Comput. 25(4):577–591, 2016, Theorem 1

import Mathlib
import Definitions.Def_BilateralProfitRegular_Proc

namespace BilateralProfitRegular

open MeasureTheory

/-- **Bernoulli factory for `B₀`** (the step "First, represent the reference probability by a bit
`B₀ ∼ Ber(P(z)/(20P̂(w)))` …"), Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256
e91e8127…), proof of Lemma 6.5, p.42 (PDF 44); cited from M. Huber, *Nearly optimal Bernoulli
factories for linear functions*, Combin. Probab. Comput. 25(4):577–591, 2016, Theorem 1, together
with the thinning step for multipliers at most `1`.

There is a universal `C` such that for every multiplier `c > 0` there is a procedure that, given
i.i.d. coins of an unknown bias `p ∈ [0, 1]` with `c·p ≤ 1/2`, outputs a bit of mean `c·p`
(it stops almost surely and outputs `true` with probability exactly `c·p`) using at most
`C·max(1, c)` coin flips in expectation. In the paper `c = 1/(20 P̂(w))` with `P̂(w) ∈ [δ, 1]`,
`p = P(z)`, and the cost is `O(1/P̂(w))`.

**Formalization Note.** A factory is a `Proc` whose only query is "flip the coin" (`Unit`); the
coin is Bernoulli(`p`) (`prob = fun _ => p`). It is chosen before `p`, so it never sees `p`. -/
theorem huber_factory :
    ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (F : Proc Unit Bool Ω),
        ∀ p : ℝ, 0 ≤ p → p ≤ 1 → c * p ≤ 1 / 2 →
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = none} = 0 ∧
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = some true} = ENNReal.ofReal (c * p) ∧
          F.expRounds (fun _ => p) Pω ≤ ENNReal.ofReal (C * max 1 c) := by sorry

end BilateralProfitRegular
