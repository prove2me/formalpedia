-- Prove2me | Theorems.Thm_Diaz_forced_plane_exhaustion
-- name    : Diaz.forced_plane_exhaustion
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:28.679111+00:00
-- url     : https://prove2.me/theorems/41093341-5175-44d1-abd5-28aa6d5a0460
-- title:
--   Homogeneous exhaustion of the forced conjugation plane of a candidate
-- statement:
--   **Nothing homogeneous distinguishes a candidate inside its own forced plane.**
--
--   Let $K \subseteq \mathbb{C}$ be a subfield, $u \neq 0$ transcendental over $K$ with $u \bar u \in K$
--   (the algebraic shape of a Diaz candidate: $\rho = u\bar u$ lies in the base field). If
--   $c_0, \ldots, c_d \in K$ satisfy
--
--   $$\sum_{i=0}^{d} c_i \, u^{i} \, \bar u^{\,d-i} = 0,$$
--
--   then every $c_i$ vanishes.
--
--   **Why.** Because $u\bar u \in K$ and $u$ is transcendental over $K$, the ratio $u/\bar u = u^2/\rho$ is
--   again transcendental over $K$: if it were algebraic then $u^2$ would be, and hence $u$. The binary-form
--   lemma then applies.
--
--   **Role.** This is the coordinate form of Carlo Perassi's homogeneous exhaustion of the forced plane:
--   a homogeneous polynomial over the base field vanishing at a tuple $x_j = a_j u + b_j \bar u$ of points of
--   $\Lambda_u = \mathbb{Q}u + \mathbb{Q}\bar u$ already vanishes identically on the corresponding
--   $\mathbb{Q}$-rational plane. Nothing is gained by adding homogeneous coordinates drawn from the plane
--   that conjugation forces on a candidate; the plane is exhausted. Together with the coordinate-invariant
--   homogenization barrier this is why the missing non-logarithmic homogenizer $1$ cannot be manufactured
--   from inside the candidate's own data.
--
--   Source: Carlo Perassi; unpublished apart from this node. No novelty is claimed; the argument
--   is elementary given the transcendence hypothesis.

import Mathlib

open ComplexConjugate

theorem Diaz.forced_plane_exhaustion {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u)
    (hu0 : u ≠ 0) (hρ : u * conj u ∈ K) (d : ℕ) (c : ℕ → ℂ) (hc : ∀ i, c i ∈ K)
    (h : ∑ i ∈ Finset.range (d + 1), c i * u ^ i * (conj u) ^ (d - i) = 0) :
    ∀ i ∈ Finset.range (d + 1), c i = 0 := by sorry
