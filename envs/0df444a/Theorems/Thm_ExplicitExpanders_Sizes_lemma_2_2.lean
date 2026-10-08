-- Prove2me | Theorems.Thm_ExplicitExpanders_Sizes_lemma_2_2
-- name    : ExplicitExpanders.Sizes.lemma_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:34:10.424718+00:00
-- url     : https://prove2.me/theorems/fc35708b-e09a-4d0f-a4cc-db1f2c01ed6f
-- title:
--   Lemma 2.2 — every large $n$ has an LPS vertex count $Q(q_1,q_2,s,t)\in[n,n+o(n)]$
-- statement:
--   Let $q_1$ and $q_2$ be distinct primes, and let
--
--   $$
--   Q(q_1,q_2,s,t)=q_1^{3(s-1)}\,q_2^{3(t-1)}\cdot\frac{q_1(q_1-1)(q_1+1)}{2}\cdot\frac{q_2(q_2-1)(q_2+1)}{2}
--   $$
--
--   be the arithmetic expression for the number of vertices of the Lubotzky–Phillips–Sarnak graph $H(p,q_1^sq_2^t)$ when the graph construction's congruence conditions hold. Then there is a function $g:\mathbb N\to\mathbb R$ with $g(n)=o(n)$ as $n\to\infty$ such that for every sufficiently large integer $n$ there are positive integers $s,t$ with
--
--   $$
--   n\le Q(q_1,q_2,s,t)\le n+g(n).
--   $$
--
--   Equivalently, for fixed distinct primes $q_1,q_2$, the ratio between consecutive elements of $\{Q(q_1,q_2,s,t): s,t\ge1\}$ tends to $1$ as the elements grow. Combined with the Ramanujan property of the LPS graphs, this gives explicit $(n,d,\lambda)$-graphs whose number of vertices is within a factor $1+o(1)$ of any prescribed large $n$, with $q_1,q_2$ fixed, which is what makes the construction of Proposition 1.1 strongly explicit for every fixed degree.
--
--   **Formalization Note** The paper's "$n\le Q\le n+o(n)$" is formalized literally: there exists $g$ with $g=o(n)$ (Mathlib's `Asymptotics.IsLittleO` along `atTop`), chosen once for the fixed pair $q_1,q_2$, and the conclusion holds eventually in $n$ (`∀ᶠ n in atTop`). An equivalent form is: for every $\mu>0$ there is $N$ such that every $n\ge N$ admits $s,t\ge1$ with $n\le Q(q_1,q_2,s,t)\le(1+\mu)n$. The lower bound $n\le Q$ is in $\mathbb N$; the upper bound is in $\mathbb R$. The positivity $s,t\ge1$ is required, as in the paper.
-- source:
--   N. Alon, Explicit expanders of every degree and size, arXiv:2003.11673v1, p. 7, Lemma 2.2

import Mathlib
import Definitions.Def_ExplicitExpanders_Sizes_Q

namespace ExplicitExpanders.Sizes

open Filter Asymptotics

/-- Lemma 2.2 (Alon, *Explicit expanders of every degree and size*, arXiv:2003.11673v1, p. 7):
let `q₁, q₂` be distinct primes. Then for every large integer `n` there are positive integers
`s, t` so that `n ≤ Q(q₁, q₂, s, t) ≤ n + o(n)`. The `o(n)` is an explicit function `g` with
`g = o(n)`, chosen once for the fixed pair `q₁, q₂`. -/
theorem lemma_2_2 {q₁ q₂ : ℕ} (hq₁ : q₁.Prime) (hq₂ : q₂.Prime) (hne : q₁ ≠ q₂) :
    ∃ g : ℕ → ℝ, g =o[atTop] (fun n : ℕ => (n : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop, ∃ s t : ℕ, 1 ≤ s ∧ 1 ≤ t ∧
        n ≤ Q q₁ q₂ s t ∧ (Q q₁ q₂ s t : ℝ) ≤ (n : ℝ) + g n := by sorry

end ExplicitExpanders.Sizes
