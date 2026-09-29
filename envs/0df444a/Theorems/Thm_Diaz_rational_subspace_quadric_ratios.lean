-- Prove2me | Theorems.Thm_Diaz_rational_subspace_quadric_ratios
-- name    : Diaz.rational_subspace_quadric_ratios
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T09:15:35.437231+00:00
-- url     : https://prove2.me/theorems/9f8d19b3-9c4b-42ce-bd29-8d44ffbef9e4
-- title:
--   Coordinate ratios on a rational subspace of the quadric z1 z2 = z3 z4
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and let $W \subseteq \mathbb{C}^4$ be a $\mathbb{C}$-subspace which is defined over $K$ — every element of $W$ is a $\mathbb{C}$-linear combination of elements of $W$ all of whose coordinates lie in $K$ — and which is contained in the quadric
--
--   $$Q : \quad z_1 z_2 - z_3 z_4 = 0 .$$
--
--   Let $x \in W$ have all four coordinates non-zero. Then
--
--   $$\left(\frac{x_1}{x_4} \in K \ \text{ and } \ \frac{x_3}{x_2} \in K\right) \qquad\text{or}\qquad \left(\frac{x_1}{x_3} \in K \ \text{ and } \ \frac{x_4}{x_2} \in K\right).$$
--
--   (Coordinates are indexed $0,1,2,3$ in the Lean statement; here they are written $x_1,\dots,x_4$.)
--
--   **Mathematical role.** This is the usable form of the classification of $K$-rational subspaces of singular $2\times2$ matrices: a point of the quadric $z_1z_2 = z_3z_4$ with no vanishing coordinate that lies on a $K$-rational linear subspace of the quadric has one of two prescribed pairs of coordinate ratios in $K$. The identification is
--
--   $$\iota(z_1,z_2,z_3,z_4) = \begin{pmatrix} z_1 & z_3 \\ z_4 & z_2 \end{pmatrix}, \qquad \det \circ\, \iota = z_1z_2 - z_3z_4,$$
--
--   under which $W$ becomes a $K$-rational subspace of singular matrices containing a matrix with no zero entry. The first alternative is the case where the matrices of $\iota(W)$ share their image line, and the ratios are the ratios down each column; the second is the shared-kernel case, and the ratios are the ratios along each row.
--
--   **Where this sits.** Two theorems of Carlo Perassi's apply a transcendence theorem of Roy and Waldschmidt to produce exactly such a $W$, and then use exactly this conclusion.
--
--   His pair dichotomy (rational proportionality or independence) is applied at
--
--   $$x = (m u,\ \bar u,\ v,\ \bar v), \qquad m = \frac{v\bar v}{u\bar u} \in \mathbb{Q}^{\times},$$
--
--   for two candidates $u, v$ of the Diaz locus with rationally commensurable squared moduli; here $x_1x_2 - x_3x_4 = m u\bar u - v\bar v = 0$. The first alternative gives $v/\bar u \in \mathbb{Q}^\times$, the second gives $mu/v \in \mathbb{Q}^\times$; together they are the conclusion $v \in \mathbb{Q}^\times u \,\dot\cup\, \mathbb{Q}^\times \bar u$.
--
--   His mixed-coordinate rigidity at a Diaz point is applied at
--
--   $$x = \left(u,\ \bar u,\ \frac{\rho}{\mu},\ \mu\right), \qquad \rho = u\bar u ,$$
--
--   for $u$ in the Diaz locus and $\mu$ a non-zero logarithm; again $x_1x_2 - x_3x_4 = u\bar u - \rho = 0$. The first alternative gives $u/\mu \in \mathbb{Q}^\times$ and the second gives $u\mu/\rho \in \mathbb{Q}^\times$, that is $\mu \in \mathbb{Q}^\times u$ respectively $\mu \in \mathbb{Q}^\times \bar u$ — the two rays that those theorems exclude by hypothesis. The same instantiation with $(\mu_1, \mu, \nu_1, \mu_1\nu_1/\mu)$ serves a companion theorem of his.
--
--   He works with $K = \mathbb{Q}$; the argument uses only that $K$ is a field, so the node is stated over an arbitrary subfield of $\mathbb{C}$.
--
--   **What is deliberately not claimed.** The *existence* of the subspace $W$ is the whole transcendence content and is a hypothesis here, not a conclusion. In his proofs it comes from Théorème 0.2 of Roy–Waldschmidt (1997) for the pair dichotomy and from their Théorème 7.1 for the mixed-coordinate rigidity and its companion; neither is available in this Mathlib revision. What this node records is the elementary residue of those proofs once the cited theorem has been granted: everything after the step at which the quadratic theorem of Roy–Waldschmidt places the point in a vector subspace defined over $\mathbb{Q}$. It asserts nothing about algebraic independence and nothing about transcendence degrees.
--
--   **Formalization note.** "Defined over $K$" is the hypothesis $W \le \operatorname{span}_{\mathbb{C}}\{z \in W : z_i \in K \ \forall i\}$; the reverse inclusion holds for any subspace, so this says exactly that $W$ is the complex span of its $K$-rational points. The proof pushes $W$ forward along $\iota$ and applies `Diaz.rational_singular_subspace_classification`.
--
--   Elementary. Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.rational_subspace_quadric_ratios
    {K : Subfield ℂ} {W : Submodule ℂ (Fin 4 → ℂ)}
    (hK : W ≤ Submodule.span ℂ {z : Fin 4 → ℂ | z ∈ W ∧ ∀ i, z i ∈ K})
    (hQ : ∀ z ∈ W, z 0 * z 1 - z 2 * z 3 = 0)
    {x : Fin 4 → ℂ} (hx : x ∈ W) (hx0 : ∀ i, x i ≠ 0) :
    (x 0 / x 3 ∈ K ∧ x 2 / x 1 ∈ K) ∨ (x 0 / x 2 ∈ K ∧ x 3 / x 1 ∈ K) := by sorry
