-- Prove2me | Theorems.Thm_Diaz_binary_form_eq_zero
-- name    : Diaz.binary_form_eq_zero
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:27.454568+00:00
-- url     : https://prove2.me/theorems/f8fa4cbe-64ef-474f-8cc5-4d8028e367d3
-- title:
--   A homogeneous binary form over $K$ vanishing at a pair with transcendental ratio is the zero form
-- statement:
--   **A homogeneous binary form over $K$ cannot vanish at a pair whose ratio is transcendental over $K$
--   unless it is the zero form.**
--
--   Let $K \subseteq \mathbb{C}$ be a subfield, let $x, y \in \mathbb{C}$ with $y \neq 0$, and suppose the
--   ratio $x/y$ is transcendental over $K$. If $c_0, \ldots, c_d \in K$ satisfy
--
--   $$\sum_{i=0}^{d} c_i \, x^{i} y^{\,d-i} = 0,$$
--
--   then $c_i = 0$ for every $i \leq d$.
--
--   **Why.** Divide by $y^{d}$: the sum becomes $\sum_i c_i (x/y)^i$, the value at $x/y$ of a polynomial with
--   coefficients in $K$. Transcendence of the ratio forces that polynomial to be zero, hence every $c_i = 0$.
--   No factorisation of the form into linear factors is needed.
--
--   **Role.** This is the algebraic step that two rigidity statements of Carlo Perassi's run on. It
--   appears twice: in his lemma that two logarithms are rigid, where a $t \times t$ minor of a matrix with
--   entries in $k\lambda_1 + k\lambda_2$ is a binary form of degree $t$ evaluated at $(\lambda_1, \lambda_2)$
--   and Baker's theorem supplies the transcendence of the ratio; and in the homogeneous exhaustion of the forced
--   plane (`Diaz.forced_plane_exhaustion`), where the pair is $(u, \bar u)$ for a candidate $u$. Isolating it makes visible that the deep
--   input enters only through the single hypothesis "the ratio is transcendental over $K$".
--
--   Source: Carlo Perassi; unpublished apart from this node. The statement in this generality is elementary. No novelty is claimed.

import Mathlib

open ComplexConjugate

theorem Diaz.binary_form_eq_zero {K : Subfield ℂ} {x y : ℂ} (hy : y ≠ 0)
    (hxy : Transcendental K (x / y)) (d : ℕ) (c : ℕ → ℂ) (hc : ∀ i, c i ∈ K)
    (h : ∑ i ∈ Finset.range (d + 1), c i * x ^ i * y ^ (d - i) = 0) :
    ∀ i ∈ Finset.range (d + 1), c i = 0 := by sorry
