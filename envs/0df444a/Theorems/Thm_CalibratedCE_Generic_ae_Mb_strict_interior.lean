-- Prove2me | Theorems.Thm_CalibratedCE_Generic_ae_Mb_strict_interior
-- name    : CalibratedCE.Generic.ae_Mb_strict_interior
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:08:37.50765+00:00
-- url     : https://prove2.me/theorems/e2a51e10-7aad-4c62-9ba6-4f8bbfb82457
-- title:
--   Proof of Theorem 2 (p. 47) — for almost every payoff matrix, every nonempty $M_b(x)$ has relative interior
-- statement:
--   Identify player 1's payoff matrix $u_1$ with a point of $\mathbb{R}^{mn}$, with Lebesgue measure. For almost every $u_1$ the following holds: for every $x\in S(1)$, if $M_b(x)$ is nonempty then there is a probability vector $p$ over $S(2)$ with all entries strictly positive at which $x$ is the unique best response,
--   $$\sum_y p(y)\,u_1(x',y) < \sum_y p(y)\,u_1(x,y)\qquad\text{for all } x' \ne x.$$
--   Such a $p$ has a neighbourhood in the simplex contained in $M_b(x)$, so $M_b(x)$ is either empty or has nonempty interior relative to the simplex.
--
--   The paper writes: "Almost every game has the property that all the sets $M_b(x)$ have non-empty interior. [...] observe that $M_b(x)$ is formed by the intersection of half-spaces. Start with a closed convex set with nonempty interior, $C$, say, and add these half-spaces one at a time. [...] We claim that the intersection of $C$ and $H$ is either the empty set or a set with an open interior." This theorem is that claim, applied to all the half-spaces defining $M_b(x)$.
--
--   **Formalization Note** The first sentence quoted is false as written: a strictly dominated strategy $x$ has $M_b(x) = \emptyset$, and games with a strictly dominated strategy form an open set of positive measure. The paper's own argument proves the corrected dichotomy "empty or with interior", which is what is stated here. "Interior" is relative to the simplex (whose interior in $\mathbb{R}^n$ is empty). Player 2's version is the same statement for the transposed matrix $u_2$.
-- source:
--   Foster and Vohra, Calibrated learning and correlated equilibrium, Games Econ. Behav. 21 (1997), p. 47, proof of Theorem (Theorem 2) (genericity of M_b(x))

import Mathlib
import Definitions.Def_CalibratedCE_Generic_Game

namespace CalibratedCE.Generic

theorem ae_Mb_strict_interior (m n : ℕ) :
    ∀ᵐ u₁ : Fin m → Fin n → ℝ ∂MeasureTheory.volume, ∀ a, (Mb u₁ a).Nonempty →
      ∃ p : Fin n → ℝ, (∀ b, 0 < p b) ∧ ∑ b, p b = 1 ∧
        ∀ a', a' ≠ a → ∑ b, p b * u₁ a' b < ∑ b, p b * u₁ a b := by sorry

end CalibratedCE.Generic
