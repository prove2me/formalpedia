-- Prove2me | Theorems.Thm_DeepQOperator_Supplement_theorem_9
-- name    : DeepQOperator.Supplement.theorem_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T13:44:42.8262+00:00
-- url     : https://prove2.me/theorems/a46409d7-db2e-48ac-b641-2710eb51a6bd
-- title:
--   Theorem 9, p.27 — bounded continuous addressing on the promise $P_{\mathrm{code}}$
-- statement:
--   For every $m\ge2$ and $0<\gamma<1$, on the promise family (50)–(51) with $r=\lceil\log_2m\rceil$ and $n=2^r$: all input coordinates and raw critic values lie in $[-1,1]$, every raw affine coefficient vector has $\ell_1$ norm at most one, and there are three rows and $3m+n<5m$ raw sites. Moreover:
--
--   1. A deterministic adaptive raw algorithm uses $r+1$ exact queries for zero regret. Each reply can be a single bit: a deterministic adaptive raw protocol with $r+1$ one-bit replies has zero regret on the whole promise.
--   2. For every randomized fixed arbitrary-affine design and every fixed affine scalar-reply protocol,
--   $$
--   \mathfrak C^{\mathrm{fixed,aff,ran}}_N\ \ge\ \frac{\gamma(m-N)_+}{64\pi^2m},\qquad \mathfrak C^{\mathrm{fixed,aff,bit}}_B\ \ge\ \frac{\gamma(m-B)_+}{64\pi^2m}. \tag{52}
--   $$
--   A fixed raw design has zero regret with $m+r$ one-bit replies.
--   3. For randomized adaptive arbitrary-affine scalar-reply protocols,
--   $$
--   \mathfrak C^{\mathrm{adaptive,aff,bit}}_B\ \ge\ \frac{\gamma\big(m-(2^B-1)\big)_+}{64\pi^2m}. \tag{53}
--   $$
--   When $m=2^r$ the exact adaptive reply-bit complexity is therefore $r+1$, even for the stronger arbitrary-affine oracle.
--
--   The promise family gives exact logarithmic reply-bit addressing with bounded features.
--
--   Differences from the source:
--   - encoding: worst-input expected regret $\sup_\theta E_\omega \ell(A(\theta;\omega),\theta)$ → an $\mathbb{R}_{\ge0}\cup\{\infty\}$-valued supremum of lower Lebesgue integrals of the loss; reason: Lean convention; the loss is nonnegative and bounded, so the values agree
--   - encoding: at most $N$ queries (reply bits) on every input and random path → the algorithm is run with fuel $N$ (protocols: hard budget `HardBudgetOn` and fuel $B$); reason: a run with fuel $N$ asks at most $N$ queries, and an algorithm with hard budget $N$ behaves identically under fuel $N$
--   - encoding: a fixed design of at most $N$ affine measurements → an `ExactDesign` with exactly $N$ rows, zero rows allowed; reason: a zero row is a known constant, so padding to $N$ rows changes nothing
--   - encoding: randomized algorithm with private seed; deterministic algorithm → seed space a standard Borel probability space $(\Omega,\mu)$; deterministic = seed space `Unit` with the Dirac measure; reason: the standing randomization model (20), §5, p.8
--   - encoding: the minimax value is at least $x$ → every algorithm of the class (measurable, on every standard Borel probability seed space) has worst regret at least $x$; reason: an infimum is at least $x$ exactly when every member is
--   - reading: a fixed raw design has zero regret with $m+r$ one-bit replies → a deterministic fixed raw protocol with $m+r$ one-bit replies and zero worst regret; reason: the proof (App. G.1, p.28) queries all $m$ payload threshold bits and $r$ address sign bits in advance, deterministically
--   - reading: when $m=2^r$ the exact adaptive reply-bit complexity is $r+1$ → for $m=2^r$, every measurable adaptive affine protocol with hard budget $r$ has positive worst regret; $r+1$ one-bit raw replies are exact by part 1; reason: exact complexity is two-sided
--   - encoding: there are $3m+n$ raw sites → an injective listing of the raw dictionary by $3m+n$ indices; reason: the listed sites are pairwise distinct
-- source:
--   Qi, Deep Q-Operator: Fixed-Accuracy Adaptive Information and Shared Bellman Decisions, STOC 2027 submission (manuscript sha256 9f8f3285…), Theorem 9 and eqs. (50)–(53), p.27 (PDF p.30); proof in Appendix G, pp.28–30

import Mathlib
import Definitions.Def_DeepQOperator_Family
import Definitions.Def_DeepQOperator_ExactDesign
import Definitions.Def_DeepQOperator_ReplyProtocol
import Definitions.Def_DeepQOperator_Supplement_AdaptiveAlg
import Definitions.Def_DeepQOperator_Supplement_Promise

open MeasureTheory

namespace DeepQOperator.Supplement

/-- **Theorem 9 (Bounded continuous addressing)** (Q. Qi, *Deep Q-Operator: Fixed-Accuracy Adaptive
Information and Shared Bellman Decisions*, STOC 2027 submission (manuscript sha256 9f8f3285…),
Theorem 9, p.27, PDF p.30; proved in Appendix G, pp.28–30).

For every `m ≥ 2` and `0 < γ < 1`, on the promise family (50)–(51) (`r = ⌈log₂ m⌉`, `n = 2^r`):
all input coordinates and raw values lie in `[-1, 1]`, every raw coefficient vector has `ℓ₁` norm at
most one, and the three rows have `3m + n < 5m` raw sites. Moreover:
1. a deterministic adaptive raw algorithm with `r + 1` exact queries has zero regret, and so does a
   deterministic adaptive raw scalar-reply protocol with `r + 1` one-bit replies;
2. every randomized fixed arbitrary-affine design has `ℭ^{fixed,aff,ran}_N ≥ γ(m - N)₊/(64π²m)` and
   every fixed affine scalar-reply protocol `ℭ^{fixed,aff,bit}_B ≥ γ(m - B)₊/(64π²m)` (52); a fixed raw
   design has zero regret with `m + r` one-bit replies;
3. every randomized adaptive affine scalar-reply protocol has
   `ℭ^{adaptive,aff,bit}_B ≥ γ(m - (2^B - 1))₊/(64π²m)` (53); when `m = 2^r` the exact adaptive reply-bit
   complexity is therefore `r + 1`, even for affine protocols.

**Formalization Note.** The domain is the nonconvex union `promiseBox m`. Deterministic algorithms and
protocols have seed space `Unit` (Dirac measure). Exact adaptive algorithms are `AdaptiveAlg` run with
fuel `r + 1`; scalar-reply protocols are the published `ReplyProtocol`, with `UsesOneBitReplies` for
single-bit fields. Lower bounds quantify over measurable protocols on any standard Borel probability
seed space. "`3m + n` raw sites" is a listing of the dictionary by `Fin (3m + n)` without repetition. -/
theorem theorem_9 :
    ∀ m : ℕ, 2 ≤ m → ∀ γ : ℝ, 0 < γ → γ < 1 →
      (∀ θ ∈ promiseBox m, ∀ c, θ c ∈ Set.Icc (-1 : ℝ) 1) ∧
      (∀ q ∈ promiseDictionary m,
        ∑ c, |q.1 c| ≤ 1 ∧ ∀ θ ∈ promiseBox m, affEval q θ ∈ Set.Icc (-1 : ℝ) 1) ∧
      (∃ L : Fin (3 * m + nn m) → AffQuery (Coord m),
        Function.Injective L ∧ Set.range L = promiseDictionary m) ∧
      3 * m + nn m < 5 * m ∧
      (∃ A : AdaptiveAlg (Coord m) Unit, A.IsExact ∧ A.IsRaw (promiseDictionary m) ∧
        A.IsMeasurable ∧ algRegret (promiseBox m) (pLoss m γ) (Measure.dirac ()) A (rr m + 1) = 0) ∧
      (∃ P : ReplyProtocol (Coord m) Unit, P.IsMeasurable ∧ IsRawProtocol (promiseDictionary m) P ∧
        UsesOneBitReplies P ∧ P.HardBudgetOn (promiseBox m) (rr m + 1) ∧
        replyRegret (promiseBox m) (pLoss m γ) (Measure.dirac ()) P (rr m + 1) = 0) ∧
      (∀ (N : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (D : ExactDesign (Coord m) Ω N), D.IsMeasurable →
        ENNReal.ofReal (γ * max 0 ((m : ℝ) - N) / (64 * Real.pi ^ 2 * m)) ≤
          designRegret (promiseBox m) (pLoss m γ) μ D) ∧
      (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (P : ReplyProtocol (Coord m) Ω),
        P.IsMeasurable → P.IsFixed → P.HardBudgetOn (promiseBox m) B →
        ENNReal.ofReal (γ * max 0 ((m : ℝ) - B) / (64 * Real.pi ^ 2 * m)) ≤
          replyRegret (promiseBox m) (pLoss m γ) μ P B) ∧
      (∃ P : ReplyProtocol (Coord m) Unit, P.IsMeasurable ∧ IsRawProtocol (promiseDictionary m) P ∧
        P.IsFixed ∧ UsesOneBitReplies P ∧ P.HardBudgetOn (promiseBox m) (m + rr m) ∧
        replyRegret (promiseBox m) (pLoss m γ) (Measure.dirac ()) P (m + rr m) = 0) ∧
      (∀ (B : ℕ) (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (P : ReplyProtocol (Coord m) Ω),
        P.IsMeasurable → P.HardBudgetOn (promiseBox m) B →
        ENNReal.ofReal (γ * max 0 ((m : ℝ) - ((2 : ℝ) ^ B - 1)) / (64 * Real.pi ^ 2 * m)) ≤
          replyRegret (promiseBox m) (pLoss m γ) μ P B) ∧
      (m = 2 ^ rr m →
        ∀ (Ω : Type) [MeasurableSpace Ω] [StandardBorelSpace Ω] (μ : Measure Ω)
          [IsProbabilityMeasure μ] (P : ReplyProtocol (Coord m) Ω),
          P.IsMeasurable → P.HardBudgetOn (promiseBox m) (rr m) →
          0 < replyRegret (promiseBox m) (pLoss m γ) μ P (rr m)) := by sorry

end DeepQOperator.Supplement
