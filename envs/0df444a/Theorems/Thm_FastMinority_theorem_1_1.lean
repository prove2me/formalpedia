-- Prove2me | Theorems.Thm_FastMinority_theorem_1_1
-- name    : FastMinority.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:04:58.800897+00:00
-- url     : https://prove2.me/theorems/ef22e262-c04a-46b8-b6ae-040fd9e2008f
-- title:
--   Theorem 1.1 — MINORITY with $k=\Theta(\log^2 n)$ reaches consensus in $O(\log^2 n/\log k)$ expected rounds and $O(\log^2 n)$ rounds w.h.p.
-- statement:
--   Consider MINORITY on $n$ agents with binary opinions: in every synchronous round each agent samples $k$ agents independently and uniformly at random with replacement (itself included) and adopts the opinion that appears fewer times in its sample, or the sample's opinion if the sample is unanimous. Let $k$ be odd with $k=\Theta(\log^2 n)$ and let $T$ be the first round at which all agents hold the same opinion. Then:
--
--   1. There is a constant $C>0$ such that for all sufficiently large $n$ and every initial configuration,
--   $$
--   \mathbb E[T]\le C\cdot\frac{\log^2 n}{\log k} .
--   $$
--   2. For every fixed $\gamma>0$ there is a constant $C=C(\gamma)>0$ such that for all sufficiently large $n$ and every initial configuration, with probability at least $1-n^{-\gamma}$,
--   $$
--   T\le C\cdot\log^2 n .
--   $$
--
--   A polylogarithmic sample size thus suffices for MINORITY to reach consensus in polylogarithmic time from every initial configuration, with no assumption on the initial imbalance.
--
--   **Formalization Note** The dynamics is the published agent-level round `MinorityDynamics.agentStep n k ∅` (no sources). Here $k=\Theta(\log^2 n)$ is read as the band $a(\ln n)^2\le k\le A(\ln n)^2$ for arbitrary constants $0<a\le A$; all other constants are chosen after $a,A$ and before $n$, $k$ and the initial state. $\mathbb E[T]=\sum_{t\ge0}\Pr(T>t)$ is bounded through all its partial sums. Logarithms are natural.
--
--   Differences from the source:
--   - reading: k = Θ(log² n); 'for every initial state and sufficiently large n, there exists a constant C > 0' → ∀ 0 < a ≤ A (and γ), then ∃ C > 0, ∃ N, ∀ n ≥ N, ∀ odd k with a(ln n)² ≤ k ≤ A(ln n)², ∀ initial configuration ω₀; reason: the literal order (C after n and ω₀) is trivial since E[T] < ∞ for each fixed n; the band form implies the claim for every sequence k(n) = Θ(log² n)
--   - encoding: E[T] ≤ C log² n/log k → every partial sum Σ_{t<m} Pr(T > t) ≤ C log² n/log k; reason: E[T] = Σ_{t≥0} Pr(T > t), a series of nonnegative terms; the bound on all partial sums is equivalent and gives E[T] < ∞
--   - encoding: T ≤ C log² n with probability ≥ 1 − n^{−γ} → Pr(T > ⌊C log² n⌋) ≤ n^{−γ}; reason: T is an integer
--   - encoding: every initial state; the MINORITY process → every configuration ω₀ : Fin n → Bool; the published agentStep n k ∅; reason: every minority count arises from some configuration; the published round is the paper's rule with no sources
-- source:
--   Berenbrink–Giriyan–Götte–Richa, Fast Minority Dynamics with Θ(log² n)-Size Samples, STOC 2027 submission (manuscript sha256 841077e0…abcdd1), Theorem 1.1, p.2 (PDF p.4)

import Mathlib
import Definitions.Def_MinorityDynamics_Agents
import Definitions.Def_MinorityDynamics_Kernel

set_option autoImplicit false

open Classical

namespace FastMinority

/-- **Theorem 1.1** (Berenbrink–Giriyan–Götte–Richa, *Fast Minority Dynamics with Θ(log² n)-Size Samples*, STOC 2027 submission manuscript (sha256 841077e0…abcdd1), p.2 = PDF p.4): let `k` be odd with `k = Θ(log² n)` and let `T` be the
time when MINORITY achieves consensus. For every initial state and sufficiently large `n` there is a
constant `C > 0` with `E[T] ≤ C · log² n / log k`. Moreover, for every fixed `γ > 0` there is a constant
`C = C(γ) > 0` such that with probability at least `1 − n^{−γ}`, `T ≤ C · log² n`.

**Formalization Note** The dynamics is the published agent-level round `MinorityDynamics.agentStep n k ∅`
(every agent samples `k` agents uniformly with replacement, itself included, and adopts the minority
opinion of its sample, or the sample's opinion if it is unanimous; no sources). `T` is the hitting time
of the consensus configurations, and `Pr(T > t) = avoidProb … t ω₀`. `E[T] = ∑_{t ≥ 0} Pr(T > t)` is
bounded through all its partial sums. `k = Θ(log² n)` is read as the band `a (ln n)² ≤ k ≤ A (ln n)²` for arbitrary constants `0 < a ≤ A`, chosen first; every other constant is chosen after them and before `n`, `k` and the initial state. Logarithms are natural (p.5). "`T ≤ C log² n`" is
"`T ≤ ⌊C log² n⌋`" since `T` is an integer. -/
theorem theorem_1_1 :
    (∀ a A : ℝ, 0 < a → a ≤ A → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ ω₀ : Fin n → Bool, ∀ m : ℕ,
      ∑ t ∈ Finset.range m, MinorityDynamics.avoidProb (MinorityDynamics.agentStep n k ∅)
          {ω | MinorityDynamics.IsConsensus ω} t ω₀ ≤ C * Real.log n ^ 2 / Real.log k) ∧
    (∀ a A : ℝ, 0 < a → a ≤ A → ∀ γ : ℝ, 0 < γ → ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ k : ℕ, Odd k → a * Real.log n ^ 2 ≤ k → (k : ℝ) ≤ A * Real.log n ^ 2 →
      ∀ ω₀ : Fin n → Bool,
      MinorityDynamics.avoidProb (MinorityDynamics.agentStep n k ∅)
          {ω | MinorityDynamics.IsConsensus ω} ⌊C * Real.log n ^ 2⌋₊ ω₀ ≤ (n : ℝ) ^ (-γ)) := by sorry

end FastMinority
