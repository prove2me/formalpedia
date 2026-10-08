-- Prove2me | Theorems.Thm_BertsekasShreve_Contraction_fixed_point_theorem
-- name    : BertsekasShreve.Contraction.fixed_point_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T19:49:15.955124+00:00
-- url     : https://prove2.me/theorems/872e7f74-8ce9-468d-bce0-e4378d183003
-- title:
--   Fixed Point Theorem (p. 55) — an $m$-step contraction on a closed set has a unique, globally attracting fixed point
-- statement:
--   Let $E$ be a real Banach space with norm $\|\cdot\|$, let $\bar B\subseteq E$ be a nonempty closed subset, and let $L:\bar B\to\bar B$. Suppose that for some positive integer $m$ and some $\rho\in(0,1)$,
--
--   $$\|L^m(z)-L^m(z')\|\le\rho\|z-z'\|\qquad\forall z,z'\in\bar B.$$
--
--   Then $L$ has a unique fixed point $z^*\in\bar B$, and for every $z\in\bar B$,
--
--   $$\lim_{N\to\infty}\|L^N(z)-z^*\|=0.$$
--
--   The theorem is the analytic engine of Chapter 4: applied to $T$ and $T_\mu$ on $\bar B$, it produces the fixed points that Proposition 4.2 identifies with $J^*$ and $J_\mu$.
--
--   **Formalization Note** The book does not say that $\bar B$ is nonempty; the conclusion is false for $\bar B=\emptyset$, so nonemptiness is a hypothesis (in the application, $J_0\in\bar B$). $L^N$ is the $N$-fold iterate on the subtype $\bar B$.
-- source:
--   Bertsekas & Shreve, Stochastic Optimal Control: The Discrete-Time Case, Athena Scientific 1996, p. 55, Fixed Point Theorem

import Mathlib

namespace BertsekasShreve.Contraction

open Filter Topology

/-- Fixed Point Theorem, p. 55. `B̄` is a nonempty closed subset of a real Banach space `E`,
`L : B̄ → B̄`, and the `m`-th iterate of `L` is a contraction with modulus `ρ ∈ (0, 1)`. Then `L`
has a unique fixed point `z*` in `B̄`, and `‖L^N(z) − z*‖ → 0` for every `z ∈ B̄`.
Nonemptiness of `B̄` is implicit on the page (the conclusion is false for `B̄ = ∅`). -/
theorem fixed_point_theorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (Bbar : Set E) (hclosed : IsClosed Bbar) (hne : Bbar.Nonempty)
    (L : Bbar → Bbar) (m : ℕ) (hm : 0 < m) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hL : ∀ z z' : Bbar, ‖((L^[m] z : Bbar) : E) - ((L^[m] z' : Bbar) : E)‖ ≤
      ρ * ‖(z : E) - (z' : E)‖) :
    ∃ zs : Bbar, L zs = zs ∧ (∀ z : Bbar, L z = z → z = zs) ∧
      ∀ z : Bbar, Tendsto (fun N : ℕ => ‖((L^[N] z : Bbar) : E) - (zs : E)‖) atTop (𝓝 0) := by sorry

end BertsekasShreve.Contraction
