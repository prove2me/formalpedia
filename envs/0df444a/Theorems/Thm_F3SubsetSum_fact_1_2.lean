-- Prove2me | Theorems.Thm_F3SubsetSum_fact_1_2
-- name    : F3SubsetSum.fact_1_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T12:28:46.991763+00:00
-- url     : https://prove2.me/theorems/4dc68528-cc77-4555-9e5f-c0205158012c
-- title:
--   Fact 1.2 — existence thresholds for $\mathbb F_3^n$-Subset-Sum
-- statement:
--   Let $\kappa_\star=\log_2 3\approx1.5850$ and consider Problem 1.1 with $h_1,\dots,h_m\in\mathbb F_3^n$.
--
--   1. If $m\ge 2n+1$, every instance has a nonempty $S\subseteq[m]$ with $\sum_{i\in S}h_i=0$.
--   2. For every $\eta>0$ there is $c>0$ such that for all $n,m$: if $m\ge(\kappa_\star+\eta)n$ then, for uniform $h$,
--   $$\Pr[\text{a solution exists}]\ge 1-2^{-cn};$$
--   and if $m\le(\kappa_\star-\eta)n$ then $\Pr[\text{a solution exists}]\le 2^{-cn}$.
--
--   The first item is a Davenport-constant bound for $\mathbb F_3^n$; the other two locate the satisfiability threshold at $m\approx\kappa_\star n$, the information-theoretic limit that Theorem 1.3 approaches.
--
--   Differences from the source:
--   - reading: 2^{−Ω_η(n)} → ∃ c > 0 depending only on η such that the bound 2^{−cn} holds for every n and m in the range, one c for both bullets; reason: the strongest reading of Ω_η; the proof's bounds 2^{−ηn} and 2^{1−ηn} hold for all n, and each probability is < 1 in the finitely many remaining cases
-- source:
--   Kothari, Metger, O'Donnell, Shutty, Wu, Exponential quantum speedup for F_3^n-Subset-Sum? Or, rigorous classical algorithms for Binary-Error LWE, arXiv:2609.40321v1, Fact 1.2, p.4 (proof App. A, pp.41–42)

import Mathlib
import Definitions.Def_F3SubsetSum_SubsetSum

namespace F3SubsetSum

/-- **Fact 1.2** (Kothari, Metger, O'Donnell, Shutty, Wu, arXiv:2609.40321v1, Fact 1.2, p.4;
proof App. A, pp.41–42): "Let κ⋆ = log(3) ≈ 1.5850 and let η > 0 be any constant. For
Problem 1.1,
• if m ≥ 2n + 1, a solution S always exists;
• if m ≥ (κ⋆ + η) · n, a solution S exists with probability at least 1 − 2^{−Ω_η(n)};
• if m ≤ (κ⋆ − η) · n, a solution S exists with probability at most 2^{−Ω_η(n)}."

**Formalization Note** `log` is base 2 (p.4), so `κ⋆ = logb 2 3`. `2^{−Ω_η(n)}` is read as: there
is `c > 0`, depending on `η` only, such that the bound `2^{−cn}` holds for every `n` and `m` in
the stated range; one `c` serves both bullets (take the smaller). The probability is over
`h₁, …, h_m` independent and uniform in `F₃ⁿ` (`probSolvable`). -/
theorem fact_1_2 :
    (∀ n m : ℕ, 2 * n + 1 ≤ m → ∀ h : Fin m → Fin n → ZMod 3, HasZeroSubsetSum h) ∧
    ∀ η : ℝ, 0 < η → ∃ c : ℝ, 0 < c ∧ ∀ n m : ℕ,
      ((Real.logb 2 3 + η) * n ≤ m → 1 - (2 : ℝ) ^ (-(c * n)) ≤ probSolvable n m) ∧
      ((m : ℝ) ≤ (Real.logb 2 3 - η) * n → probSolvable n m ≤ (2 : ℝ) ^ (-(c * n))) := by sorry

end F3SubsetSum
