-- Prove2me | Theorems.Thm_CombOpt_HeldKarp_farkas_lemma_inequalities
-- name    : CombOpt.HeldKarp.farkas_lemma_inequalities
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-13T19:34:24.826901+00:00
-- url     : https://prove2.me/theorems/3401f5dc-5b88-4112-8b30-754f813c4dce
-- title:
--   Farkas' lemma for systems of linear inequalities ($Ax\le b$ solvable iff $yb\ge0$ whenever $y\ge0,\ yA=0$)
-- statement:
--   Let $A=(a_{is})$ be a real matrix with finitely many rows $i\in\iota$ and finitely many columns $s\in\sigma$, and let $b\in\mathbb{R}^{\iota}$. Then
--
--   $$\exists x\in\mathbb{R}^{\sigma}:\ Ax\le b \quad\Longleftrightarrow\quad \forall y\in\mathbb{R}^{\iota}_{\ge 0}:\ yA=0 \implies yb\ge 0,$$
--
--   that is, the system $Ax\le b$ has a solution if and only if $yb\ge 0$ for each row vector $y\ge 0$ with $yA=0$.
--
--   Role: the theorem of alternatives behind the LP duality step of Theorem 7.2: applied to the system "$t \le 2\sum_v y_v + \bar c(J)$ for every 1-tree $J$" in the node numbers $y$, it gives either node numbers whose Held-Karp bound is at least $t$, or a convex combination of 1-trees with all degrees equal to 2 and cost below $t$, which is a point of the subtour polytope.
--
--   **Formalization Note**: rows and columns are indexed by arbitrary finite types; $yA=0$ is stated componentwise.
-- source:
--   A. Schrijver, Theory of Linear and Integer Programming (Wiley, 1986), Section 7.3, Corollary 7.1e, p. 89; see also https://en.wikipedia.org/wiki/Farkas%27_lemma#Variants

import Mathlib

namespace CombOpt.HeldKarp

theorem farkas_lemma_inequalities {σ ι : Type*} [Fintype σ] [Fintype ι] (a : ι → σ → ℝ)
    (b : ι → ℝ) :
    (∃ x : σ → ℝ, ∀ i, ∑ s, a i s * x s ≤ b i) ↔
      ∀ l : ι → ℝ, (∀ i, 0 ≤ l i) → (∀ s, ∑ i, l i * a i s = 0) → 0 ≤ ∑ i, l i * b i := by sorry

end CombOpt.HeldKarp
