-- Prove2me | Theorems.Thm_EliasGlobalClock_LowerBound_Supplement_theorem_3_1
-- name    : EliasGlobalClock.LowerBound.Supplement.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T07:36:52.89559+00:00
-- url     : https://prove2.me/theorems/f17adba5-eded-444f-be14-ceebd6a71639
-- title:
--   Theorem 3.1 — Algorithm 1 has latency O(f(⌈log(n+1)⌉) log(1/ϵ(n))), and O(P log(1/ϵ(n))) with MonoElias
-- statement:
--   Let $f:\mathbb Z_+\to\mathbb Z_+$ be nondecreasing with $\sum_{N\ge1}1/f(N)<K<\infty$. A *latency function* $L(n,\epsilon)$ of a leader-election protocol, for a fixed nonincreasing error profile $\epsilon$, guarantees that for every $n\ge1$, every first wake-up slot $t_0$ and every wake-up pattern of at most $n$ players starting at $t_0$, the first success $t^*$ satisfies $\Pr(t^*-t_0>L(n,\epsilon))<\epsilon(n)$.
--
--   1. There is a prefix-free code and a constant $C>0$ such that, for every nonincreasing $\epsilon:\mathbb Z_+\to(0,1/2)$, Algorithm 1 (LeaderElection) with that code has a latency function with
--   $$L(n,\epsilon)\le C\,f(\lceil\log_2(n+1)\rceil)\,\ln\frac1{\epsilon(n)}\qquad(n\ge1).$$
--   2. There is a constant $C>0$ such that, for every such $\epsilon$, Algorithm 1 with $\mathrm{Code}=\mathrm{MonoElias}$ has a latency function with, for all $n\ge1$,
--   $$L(n,\epsilon)\le C\,P\,\ln\frac1{\epsilon(n)},\quad P=2^{|\mathrm{MonoElias}(\lceil\log_2(n+1)\rceil)|+1},\qquad L(n,\epsilon)\le C\,\Big(\prod_{h=1}^{\log^*n}\log_2^{(h)}n\Big)\,2^{\log^*n}\ln\frac1{\epsilon(n)}.$$
--
--   The paper states both bounds with $O(\cdot)$; the constants here are fixed before $\epsilon$ and $n$ (in clause 1 they may depend on $f$ and $K$). Its proof gives success probability at least $1/(2\sqrt e)$ in each aligned interval of length $P$, so a budget of order $P\log(1/\epsilon(n))$ suffices uniformly over wake-up patterns; for the generic code $P\le4Kf(\lceil\log_2(n+1)\rceil)$. This upper bound is matched by the mission's goal, Theorem 4.1.
--
--   Differences from the source:
--   - encoding: a latency function L(n,ϵ): Pr(t*−t₀ > L(n,ϵ)) < ϵ(n) for any pattern of spontaneous wake-ups starting at t₀ → the published IsLatency at the fixed profile ϵ: a natural budget L(n) with strict failure < ϵ(n) for every first wake-up slot and every wake-up pattern of at most n players; reason: this is the published base model of the mission, shared with Theorem 4.1
--   - encoding: Algorithm 1 with fresh choices independent conditional on the past → a published StreamProtocol on a trivial shared input whose per-player streams are products of Bernoulli(2^(−Int(t))) laws, stopped at the first singleton by the published coupling; reason: Algorithm 1 is memoryless under FAIL feedback, so its attempts are independent Bernoulli choices until the first success
--   - reading: There exists a LeaderElection protocol that guarantees latency … → there is a prefix-free code such that Algorithm 1 (LeaderElection) with that code guarantees the latency; reason: LeaderElection is Algorithm 1, whose only free parameter is the code; the reading is the stronger one
--   - reading: L(n,ϵ) = O(·) in both clauses → ∃ C > 0, fixed before ϵ and n, with the bound for every n ≥ 1 (one latency function satisfying both bounds of clause 2); reason: the proof gives a budget P(⌈ln(1/ϵ(n))/ln(10/7)⌉+2), uniform in ϵ and n; ϵ < 1/2 makes ln(1/ϵ(n)) ≥ ln 2 so additive terms are absorbed
--   - encoding: log(1/ϵ(n)) with log base 2 → Real.log (natural logarithm); reason: the two differ by the factor ln 2, absorbed in C
--   - encoding: log n log log n log log log n ⋯ 1 · 2^(log* n) → ∏_{h=1}^{log* n} log₂^(h) n · 2^(log* n), with log* n = min{ℓ : log₂^(ℓ) n < 2}; reason: the dots run over the iterates up to the last one that is still at least 1, as fixed by log*; an empty product is 1
-- source:
--   Kuowen Chen, Shengquan Du, Tsvi Kopelowitz, Seth Pettie, Ben Plosk, STOC 2027 submission #1311 (October 2026), The Necessity of Elias Codes in the Global Clock Model, printed p.8 / PDF p.9, Theorem 3.1 and its proof; Algorithm 1 and the latency definition printed p.7 / PDF p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1311.pdf

import Definitions.Def_EliasGlobalClock_LowerBound_Supplement_algorithmOne

open MeasureTheory

namespace EliasGlobalClock.LowerBound.Supplement

/-- Theorem 3.1 (printed p.8 / PDF p.9). Let `f : ℤ₊ → ℤ₊` be nondecreasing with
`∑_N 1/f(N) < K < ∞`.
(1) There is a prefix-free code such that Algorithm 1 (LeaderElection) with that code has, for
every nonincreasing `ϵ : ℤ₊ → (0, 1/2)`, a latency function `L(n, ϵ)` (in the published sense
`IsLatency`: strict failure `< ϵ(n)` uniformly over first wake-up times and wake-up patterns
of at most `n` players) with `L(n, ϵ) ≤ C f(⌈log(n+1)⌉) ln(1/ϵ(n))` for all `n`.
(2) Algorithm 1 with `Code = MonoElias` has a latency function with
`L(n, ϵ) ≤ C P ln(1/ϵ(n))`, `P = 2^{|MonoElias(⌈log(n+1)⌉)|+1}`, and
`L(n, ϵ) ≤ C (log n · log log n ⋯) 2^{log* n} ln(1/ϵ(n))`.
The constants `C` are fixed before `ϵ` and `n`. -/
theorem theorem_3_1 (f : ℕ+ → ℕ+) (hf : Monotone f) (K : ℝ)
    (hsum : Summable (fun N : ℕ+ => (1 : ℝ) / (f N : ℝ)))
    (hK : ∑' N : ℕ+, (1 : ℝ) / (f N : ℝ) < K) :
    (∃ c : ℕ+ → List Bool, IsPrefixFree c ∧ ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℕ+ → ℝ, ErrorProfile ε → (∀ n, ε n < 1 / 2) →
        ∃ L : ℕ+ → ℕ, IsLatency (Measure.dirac ()) (algorithmOne c) ε L ∧
          ∀ n : ℕ+, (L n : ℝ) ≤ C * (f (ceilLog n) : ℝ) * Real.log (1 / ε n)) ∧
    (∃ C : ℝ, 0 < C ∧
      ∀ ε : ℕ+ → ℝ, ErrorProfile ε → (∀ n, ε n < 1 / 2) →
        ∃ L : ℕ+ → ℕ, IsLatency (Measure.dirac ()) (algorithmOne monoElias) ε L ∧
          (∀ n : ℕ+, (L n : ℝ) ≤
            C * (2 : ℝ) ^ ((monoElias (ceilLog n)).length + 1) * Real.log (1 / ε n)) ∧
          (∀ n : ℕ+, (L n : ℝ) ≤
            C * iterLogProduct n * (2 : ℝ) ^ logStar n * Real.log (1 / ε n))) := by sorry

end EliasGlobalClock.LowerBound.Supplement
