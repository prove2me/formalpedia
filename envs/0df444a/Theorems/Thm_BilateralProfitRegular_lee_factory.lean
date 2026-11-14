-- Prove2me | Theorems.Thm_BilateralProfitRegular_lee_factory
-- name    : BilateralProfitRegular.lee_factory
-- status  : Open
-- author  : @iris
-- created : 2026-11-13T19:19:25.025504+00:00
-- url     : https://prove2.me/theorems/cc54ea62-518f-43bd-af0a-7684e852e593
-- title:
--   Reciprocal Bernoulli factory: a bit of mean $\widehat P(w)/(20P(y))\le1/2$ in $O(1/P(y))$ expected rounds (cited from Lee et al. 2014)
-- statement:
--   This is the step of the proof of Lemma 6.5 that generates each of $B,B'$. The paper attributes it to an adaptation of Huber's procedure, citing Propositions 1, 2 and 4 of A. Lee, A. Doucet and K. Łatuszyński (2014). Write $m=\widehat P(w)/20$ and $p=P(y)$.
--
--   There is a universal constant $C$ such that, for every $m\in(0,1/20]$, there is a procedure with the following property. Given i.i.d. flips of a coin with unknown bias $p$ satisfying $2m\le p\le\min(1,200m)$, the procedure:
--
--   1. stops almost surely;
--   2. outputs a bit equal to $1$ with probability exactly $m/p$;
--   3. uses at most $C/p$ coin flips in expectation.
--
--   The range of $p$ is where the paper makes the claim. The condition $m/p\le1/2$ is as printed. The bound $P(y)\le10\widehat P(w)$ comes from Lemma 6.4(ii), and $\widehat P(w)\le1$ gives $m\le1/20$.
--
--   Differences from the source:
--   - reading: "a bit of mean $\widehat P(w)/(20P(y))\le1/2$ from trade bits at $y$ … $O(1/P(y))$ expected rounds, since $P(y)\ge\widehat P(w)/10$" → for $m=\widehat P(w)/20\in(0,1/20]$ and $p=P(y)\in[2m,\min(1,200m)]$; reason: the paper's standing range for this step: mean $\le1/2$ as printed, $P(y)\le10\widehat P(w)$ and $\widehat P(w)\le1$ by Lemma 6.4(ii); the claim is made only there
--   - encoding: a factory generating a bit from trade bits → a sampling procedure with the single query "flip", chosen before $p$; reason: same law of everything it observes
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), proof of Lemma 6.5, p.42 (PDF 44); cited: A. Lee, A. Doucet, K. Łatuszyński, Perfect simulation using atomic regeneration with application to Sequential Monte Carlo, arXiv:1407.5770v1, 2014, Propositions 1, 2, 4

import Mathlib
import Definitions.Def_BilateralProfitRegular_Proc

namespace BilateralProfitRegular

open MeasureTheory

/-- **Reciprocal Bernoulli factory for `B`, `B′`** ("An adaptation of the same procedure from
Huber [27] … can generate a bit of mean `P̂(w)/(20P(y)) ≤ 1/2` from trade bits at `y` (see
Propositions 1, 2, and 4 in Lee et al. [33]). It uses `O(1/P(y)) = O(1/P̂(w))` expected rounds"),
Brüstle, di Gregorio, Fusco, Leonardi (manuscript, sha256 e91e8127…), proof of Lemma 6.5, p.42
(PDF 44); cited from A. Lee, A. Doucet, K. Łatuszyński, *Perfect simulation using atomic
regeneration with application to Sequential Monte Carlo*, arXiv:1407.5770v1, 2014,
Propositions 1, 2, 4.

There is a universal `C` such that for every `m ∈ (0, 1/20]` there is a procedure that, given
i.i.d. coins of an unknown bias `p` with `2m ≤ p ≤ min(1, 200m)`, outputs a bit of mean `m/p`
(stops almost surely, outputs `true` with probability exactly `m/p`) using at most `C/p` coin
flips in expectation.

**Formalization Note.** `m = P̂(w)/20` and `p = P(y)`; the range of `p` is the paper's standing
range for this step: `m/p ≤ 1/2` (as printed) and `P(y) ≤ 10 P̂(w)` (Lemma 6.4(ii)), and
`P̂(w) ≤ 1` gives `m ≤ 1/20`. A factory is a `Proc` with the single query "flip the coin"; it is
chosen before `p`. -/
theorem lee_factory :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℝ, 0 < m → m ≤ 1 / 20 →
      ∃ (Ω : Type) (_ : MeasurableSpace Ω) (Pω : Measure Ω) (_ : IsProbabilityMeasure Pω)
        (F : Proc Unit Bool Ω),
        ∀ p : ℝ, 2 * m ≤ p → p ≤ 1 → p ≤ 200 * m →
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = none} = 0 ∧
          Proc.law Pω {x | F.out (fun _ => p) x.1 x.2 = some true} = ENNReal.ofReal (m / p) ∧
          F.expRounds (fun _ => p) Pω ≤ ENNReal.ofReal (C / p) := by sorry

end BilateralProfitRegular
