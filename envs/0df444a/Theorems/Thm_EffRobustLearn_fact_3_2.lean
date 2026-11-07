-- Prove2me | Theorems.Thm_EffRobustLearn_fact_3_2
-- name    : EffRobustLearn.fact_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:35:04.784489+00:00
-- url     : https://prove2.me/theorems/2ecf7467-1c0c-4190-a106-24bcd46ccc94
-- title:
--   Fact 3.2 — weighted ERM by one call to an ERM oracle
-- statement:
--   There are universal constants $C_F,K>0$ and $D\in\mathbb N$ with the following property. Let $O$ be an ERM oracle for $C$, let $\bar S$ be a dataset with weights $w\in[-b,b]$, and let $\varepsilon,\delta>0$. The sampler with $N=\lceil C_F(b^2/\varepsilon^2)(|\bar S|+\log(1/\delta))\rceil$ draws outputs a concept $c\in C$ with exactly one call to $O$, in work at most $K(1+|\bar S|+b+1/\varepsilon+\max(0,\log(1/\delta)))^D$, such that, with probability at least $1-\delta$,
--   $$\frac1{|\bar S|}\sum_{(x,y)\in\bar S}w(x,y)c(x)y\ge\max_{c'\in C}\Big(\frac1{|\bar S|}\sum_{(x,y)\in\bar S}w(x,y)c'(x)y\Big)-\varepsilon.$$
--
--   Each Frank–Wolfe step of Algorithm 1 is an instance.
--
--   Differences from the source:
--   - reading: runs in time $\mathrm{poly}(|\bar S|,b,1/\varepsilon,\log(1/\delta))$ → unit-cost work $|\bar S|+2N+1$, bounded by $K(1+|\bar S|+b+1/\varepsilon+\max(0,\log(1/\delta)))^D$; reason: no machine is defined over an arbitrary $X$; for $\delta\ge1$ the logarithm is negative, so the base uses its positive part, and a base $\ge1$ covers every polynomial
--   - reading: weights not all zero, implicitly (a distribution is sampled) → all-zero weights give $O([\,])$; reason: every concept then satisfies the inequality
--   - encoding: $O(\cdot)$ samples, independent, with the stated law → $N$ with constant $C_F$; inverse CDF of i.i.d. uniform seed coordinates; reason: the inverse CDF has the stated law
--   - encoding: $w\in[-b,b]$ → also $0\le b$; reason: says that the interval is nonempty; it excludes only the empty dataset with $b<0$
--   - encoding: $\Pr[\cdot]\ge1-\delta$ → the measure of the bad set $\le\delta$, an outer measure when the set is not measurable; reason: the adversary and the oracle are arbitrary functions, so the event need not be measurable; this is the strongest reading
--   - encoding: concepts and labels in $\{\pm1\}$; samples as sets of instances → Bool values read through pm; samples as indexed families; reason: same instances; §2's sample conventions keep repeated entries distinct
-- source:
--   Klivans, Stavropoulos, Tikhonov, Vasilyan, Efficient Robust Learning at the Information-Theoretic Limit, arXiv:2609.17655 (held version, sha256 312a0857…), Fact 3.2, p.12 (PDF p.13)

import Mathlib
import Definitions.Def_EffRobustLearn_weightedERM
import Definitions.Def_EffRobustLearn_IsERMOracle

open MeasureTheory

namespace EffRobustLearn

universe u

/-- Fact 3.2 (Weighted ERM), p.12 (arXiv:2609.17655, held version, sha256 312a0857…). There are universal `C_F`, `K`, `D` such that the sampler `weightedERM` with
`N = ⌈C_F (b²/ε²)(|S̄| + log(1/δ))⌉` draws has, for every ERM oracle, dataset, weights in `[-b, b]` and `ε, δ > 0`: outer probability at most `δ` of missing
`max_{c'∈C} (1/|S̄|) ∑ w c' y` by more than `ε`; output in `C`; exactly one oracle call; polynomial work.

**Formalization Note.** The probability of the bad event is the outer measure of its seed set, since an arbitrary oracle need not be measurable.
`max_{c'∈C}` is written as an event over every `c' ∈ C`; the maximum exists because the objective takes finitely many values on `C`. `δ ≥ 1` is included, where
`log(1/δ) ≤ 0` and the claim is trivial, so the polynomial is in `max(0, log(1/δ))` with base `≥ 1`, which covers every polynomial in the four quantities. `0 ≤ b` says that the interval `[-b, b]` is nonempty. -/
theorem fact_3_2 :
    ∃ (CF K : ℝ) (D : ℕ), 0 < CF ∧ 0 < K ∧
      ∀ (X : Type u) (C : Set (X → Bool)) (O : List (X × Bool) → X → Bool), IsERMOracle C O →
        ∀ (M : ℕ) (data : Fin M → X × Bool) (w : Fin M → ℝ) (b : ℝ), 0 ≤ b → (∀ i, |w i| ≤ b) →
        ∀ ε δ : ℝ, 0 < ε → 0 < δ →
          seedStreamLaw {ω | ∃ c' ∈ C, weightedObjective data w (weightedERM O CF b ε δ data w ω).concept <
              weightedObjective data w c' - ε} ≤ ENNReal.ofReal δ ∧
          ∀ ω, (weightedERM O CF b ε δ data w ω).concept ∈ C ∧
            (weightedERM O CF b ε δ data w ω).calls = 1 ∧
            ((weightedERM O CF b ε δ data w ω).work : ℝ) ≤
              K * (1 + (M : ℝ) + b + 1 / ε + max 0 (Real.log (1 / δ))) ^ D := by sorry

end EffRobustLearn
