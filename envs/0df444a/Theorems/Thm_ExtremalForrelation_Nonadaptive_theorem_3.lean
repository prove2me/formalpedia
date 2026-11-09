-- Prove2me | Theorems.Thm_ExtremalForrelation_Nonadaptive_theorem_3
-- name    : ExtremalForrelation.Nonadaptive.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:58:02.431774+00:00
-- url     : https://prove2.me/theorems/9041bd26-cd2a-449c-8359-18d92008e267
-- title:
--   Theorem 3 — near-optimal non-adaptive lower bound for extremal Forrelation
-- statement:
--   Throughout, $n$ is a multiple of $4$, $m=n/2$ and $M=2^m$ (the paper's standing notation, p. 3).
--
--   Let $\mu_0,\mu_1$ be the transcript laws of the hard instances of §1.1.1 at a query set $Q$, with $q=|Q|$.
--
--   1. For every non-adaptive query set $Q$ and every integer $1\le r<m$,
--   $$\|\mu_0-\mu_1\|_{TV}\le2\binom{q}{r+2}M^{-(r+1)}+2\cdot4^{r+1}\frac{q}{M}. \tag{7}$$
--   2. In particular, every non-adaptive algorithm that solves extremal Forrelation with probability at least $2/3$ must make $2^{(1/2-o(1))n}$ queries, where the $o(1)$ term is $O(1/\sqrt n)$. Explicitly: there are absolute constants $C>0$ and $n_0$ such that for every $n\ge n_0$ with $4\mid n$, every randomized non-adaptive algorithm making at most $q$ queries that answers correctly with probability at least $2/3$ on every promised input satisfies
--   $$q\ge2^{\,n/2-C\sqrt n}.$$
--
--   This is the paper's main result (informal Theorem 1). It matches the conjectured $\tilde\Theta(2^{n/2})$ bound up to the $o(1)$ term in the exponent. For example, $C=\sqrt2$ and $n_0=452$ are admissible: with $r=\lfloor\sqrt m/2\rfloor$ and $q\le M^{1-1/(r+2)}$, (7) gives $\|\mu_0-\mu_1\|_{TV}\le2/(r+2)!+2^{2r+3-m/(r+2)}<1/3$ once $m\ge225$, and $M^{1-1/(r+2)}\ge2^{n/2-\sqrt2\sqrt n}$.
--
--   Differences from the source:
--   - encoding: 'every non-adaptive algorithm making q queries' in (7) → every query set Q ⊆ F_2^n, with q = |Q|; reason: μ_0, μ_1 depend on the algorithm only through its query set; repeated locations carry no information
--   - encoding: must make 2^{(1/2−o(1))n} queries, where the o(1) term is O(1/√n) → ∃ C > 0, ∃ n₀, ∀ n ≥ n₀ with 4 ∣ n, every solving algorithm with budget q has 2^{n/2 − C√n} ≤ q; reason: q ≥ 2^{(1/2−ε(n))n} with ε(n) ≤ C/√n for large n is exactly this; C and n₀ are absolute
--   - encoding: randomized non-adaptive algorithm; extremal Forrelation promise forr ≥ 1 or forr ≤ −1 → finite weighted family of (query set of size ≤ q, decision rule) seeds; promise forr(χ_f, χ_g) = (−1)^b; each query returns (f(x), g(x)); reason: every distribution over the finitely many deterministic algorithms is such a family; |forr| ≤ 1 makes the promises equal; paired queries are the paper's model (p. 3, footnote 2)
-- source:
--   Clément Canonne, Kenny Chen, Julian Mestre, STOC 2027 submission #61 (October 2026), Theorem 3, p. 9 (eq. (7)); proof §3.7, p. 20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/61.pdf

import Mathlib
import Definitions.Def_ExtremalForrelation_Nonadaptive_Pinning
import Definitions.Def_ExtremalForrelation_Nonadaptive_Algorithm

open Classical

namespace ExtremalForrelation.Nonadaptive

/-- Theorem 3 (p. 9). (7): for every non-adaptive query set `Q` of `q` points and every integer
`1 ≤ r < m`, `‖μ₀ − μ₁‖_TV ≤ 2 binom(q, r+2) M^{−(r+1)} + 2 · 4^{r+1} q/M`.
In particular, every (randomized) non-adaptive algorithm that solves extremal Forrelation with
probability at least `2/3` makes `2^{(1/2 − o(1)) n}` queries with the `o(1)` term `O(1/√n)`:
there are absolute constants `C > 0` and `n₀` such that for every `n ≥ n₀` divisible by `4`,
such an algorithm makes at least `2^{n/2 − C √n}` queries. -/
theorem theorem_3 :
    (∀ n : ℕ, 4 ∣ n → ∀ (Q : Finset (V n)) (r : ℕ), 1 ≤ r → r < n / 2 →
      tv (mu Q 0) (mu Q 1) ≤
        2 * (Nat.choose Q.card (r + 2) : ℝ) * (((2 : ℝ) ^ (n / 2))⁻¹) ^ (r + 1) +
          2 * (4 : ℝ) ^ (r + 1) * Q.card / 2 ^ (n / 2)) ∧
    (∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 4 ∣ n →
      ∀ (q : ℕ) (A : RandNonadaptiveAlg n q), Solves A →
        (2 : ℝ) ^ ((n : ℝ) / 2 - C * Real.sqrt n) ≤ q) := by sorry

end ExtremalForrelation.Nonadaptive
