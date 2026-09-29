-- Prove2me | Theorems.Thm_Diaz_zpow_mem_iff
-- name    : Diaz.zpow_mem_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:48.466987+00:00
-- url     : https://prove2.me/theorems/5cb4cd46-f714-4ab2-b21f-270162778856
-- title:
--   Only the zeroth integer power of a transcendental element lies in the base field
-- statement:
--   **Only the zeroth integer power of a transcendental element lands back in the base field.**
--
--   Let $K \subseteq \mathbb{C}$ be a subfield and $u \neq 0$ transcendental over $K$. Then for
--   $n \in \mathbb{Z}$,
--
--   $$u^{n} \in K \iff n = 0.$$
--
--   **Why.** If $u^n \in K$ then $u^n$ is algebraic over $K$, hence lies in the field of elements algebraic
--   over $K$; for $n > 0$ this makes $u$ algebraic over $K$, and for $n < 0$ the same applies to
--   $u^{-n} = (u^n)^{-1}$, since that field is closed under inversion.
--
--   **Role.** This is the sparsity input Carlo Perassi's unpublished argument uses twice. In his Laurent consistency model it is the
--   statement that $\{n \in \mathbb{Z} : T^n \in \widetilde{\mathcal L}_0\} = \{-1, 0, 1\}$ — the powers of
--   the generator are sparse, and his isomorphism theorem transports that to the candidate's hull $W_u$. In
--   his balanced-jet proposition it is what makes $u^j \bar u^{\,k}$ algebraic exactly on the diagonal
--   $j = k$: after substituting $\bar u = \rho/u$, the jet is an algebraic multiple of $u^{\,j-k}$.
--
--   Source: Carlo Perassi, unpublished apart from this node: the sparse-power clause of his Laurent consistency model and the transcendence
--   step in his balanced lattice jets. The statement in this generality is elementary. No novelty is claimed.

import Mathlib

open ComplexConjugate

theorem Diaz.zpow_mem_iff {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0) (n : ℤ) :
    u ^ n ∈ K ↔ n = 0 := by sorry
