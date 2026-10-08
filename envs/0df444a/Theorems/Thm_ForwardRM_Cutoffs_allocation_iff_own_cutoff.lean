-- Prove2me | Theorems.Thm_ForwardRM_Cutoffs_allocation_iff_own_cutoff
-- name    : ForwardRM.Cutoffs.allocation_iff_own_cutoff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:32.719055+00:00
-- url     : https://prove2.me/theorems/b2a339db-cbf6-42bc-bda5-c384373447eb
-- title:
--   Lemma 2 — with cutoffs decreasing in j, unit j is allocated iff y^{k−j+1} ≥ x^j_t
-- statement:
--   Fix a period $t$ and a seller with $k$ units. Let $y^1\ge y^2\ge\cdots\ge y^k$ be the values of the buyers present and let $x^\ell_t=x^\ell_t(\mathbf y^{-(k-\ell+1)})$, $\ell\in\{1,\dots,k\}$, be the period-$t$ cutoffs at these buyers. Within the period the seller allocates the $j$-th unit if and only if $y^{k-\ell+1}\ge x^\ell_t$ for all $\ell\in\{j,\dots,k\}$. If the cutoffs are decreasing in $\ell$, then for every $j\in\{1,\dots,k\}$
--
--   $$
--   \big(\forall \ell\in\{j,\dots,k\}:\ y^{k-\ell+1}\ge x^\ell_t\big)\iff y^{k-j+1}\ge x^j_t .
--   $$
--
--   So each unit can be treated separately, by comparing its own cutoff with the value of the buyer in the corresponding position.
--
--   **Formalization Note** This is a statement about the within-period allocation rule only: the values are any real sequence decreasing on $\{1,\dots,k\}$ and the cutoffs any real sequence decreasing on $\{1,\dots,k\}$.
-- source:
--   Board, Skrzypacz, Revenue Management with Forward-Looking Buyers, J. Political Economy 124(4) (2016), accepted manuscript of Feb. 6, 2015, p. 14, Lemma 2 (allocation rule stated on p. 13)

import Mathlib

namespace ForwardRM.Cutoffs

/-- Lemma 2 (Board–Skrzypacz, p. 14). Within period `t` the seller with `k` units allocates the
`j`-th unit iff `y^{k−ℓ+1} ≥ x^ℓ_t` for all `ℓ ∈ {j, …, k}`, where `y¹ ≥ y² ≥ ⋯` are the buyers'
values and `x^ℓ_t = x^ℓ_t(y^{−(k−ℓ+1)})` the period-`t` cutoffs at the given buyers. If these cutoffs
are decreasing in `ℓ`, the `j`-th unit is allocated iff `y^{k−j+1} ≥ x^j_t`. -/
theorem allocation_iff_own_cutoff (k : ℕ) (y x : ℕ → ℝ)
    (hy : AntitoneOn y (Set.Icc 1 k)) (hx : AntitoneOn x (Set.Icc 1 k))
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (∀ ℓ, j ≤ ℓ → ℓ ≤ k → x ℓ ≤ y (k - ℓ + 1)) ↔ x j ≤ y (k - j + 1) := by sorry

end ForwardRM.Cutoffs
