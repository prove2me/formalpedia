-- Prove2me | Theorems.Thm_Diaz_balanced_jet_mem_iff
-- name    : Diaz.balanced_jet_mem_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:14:42.067576+00:00
-- url     : https://prove2.me/theorems/d7c06c9c-c456-4654-8d11-fb81789b7d78
-- title:
--   Balanced jets: $u^j\bar u^{\,k}\alpha$ is algebraic exactly when $j=k$
-- statement:
--   **Balanced jets, and only balanced jets, are algebraic.**
--
--   Let $K \subseteq \mathbb{C}$ be a subfield, $u \neq 0$ transcendental over $K$ with $u\bar u \in K$, and
--   let $\alpha \in K$ be non-zero. Then for $j, k \geq 0$
--
--   $$u^{j}\,\bar u^{\,k}\,\alpha \in K \iff j = k.$$
--
--   **Why.** Since $\rho = u\bar u \in K$ we may write $\bar u = \rho/u$, so
--   $u^{j}\bar u^{\,k}\alpha = (\rho^{k}\alpha)\, u^{\,j-k}$ with $\rho^k\alpha \in K^\times$. The claim
--   reduces to $u^{\,j-k} \in K \iff j = k$, which is the sparsity statement for integer powers of a
--   transcendental element.
--
--   **Role.** This is the arithmetic content of a proposition of Carlo Perassi's on balanced lattice jets. For a candidate
--   $u$ with $\alpha = e^{u}$, the function $F(z,w) = \exp(uz + \bar u w)$ has
--
--   $$\partial_z^{\,j}\partial_w^{\,k}F(m,n) = u^{j}\bar u^{\,k}\alpha^{m}\bar\alpha^{\,n},$$
--
--   and this node says that this jet is algebraic exactly on the diagonal $j = k$ — so that
--   $\Delta = \partial_z\partial_w$ acts as multiplication by $\rho$ and every balanced jet on $\mathbb{Z}^2$
--   stays in the fixed number field $\mathbb{Q}(\alpha, \bar\alpha, \rho)$. The Lean statement is the
--   algebraic dichotomy itself, stated for an arbitrary subfield and without any differential calculus, so it
--   holds unconditionally; his use of it is the case $K = \overline{\mathbb{Q}}$, with the
--   algebraic factor $\alpha^{m}\bar\alpha^{\,n}$ of the jet absorbed into the single parameter $\alpha$.
--
--   Source: Carlo Perassi; unpublished apart from this node. No novelty is claimed.

import Mathlib

open ComplexConjugate

theorem Diaz.balanced_jet_mem_iff {K : Subfield ℂ} {u : ℂ} (hT : Transcendental K u) (hu0 : u ≠ 0)
    (hρ : u * conj u ∈ K) {α : ℂ} (hα : α ∈ K) (hα0 : α ≠ 0) (j k : ℕ) :
    u ^ j * (conj u) ^ k * α ∈ K ↔ j = k := by sorry
