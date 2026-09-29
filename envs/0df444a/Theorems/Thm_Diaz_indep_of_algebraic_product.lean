-- Prove2me | Theorems.Thm_Diaz_indep_of_algebraic_product
-- name    : Diaz.indep_of_algebraic_product
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:05:22.645254+00:00
-- url     : https://prove2.me/theorems/4b093cfe-5709-4e12-a352-ed4926d7006e
-- title:
--   $1$, $\nu$ and $p$ are $K$-independent when $p\nu$ is a non-zero element of $K$
-- statement:
--   **Source.** This is Carlo Perassi's mathematics: the independence step, unpublished apart from this node, in the proof of his theorem that non-real two-point fibres force $e^{\pi^2}$ transcendental. Published on his mission with his permission. No novelty is claimed for it here; the argument is elementary.
--
--   **Statement.** Let $K \subset \mathbb{C}$ be a subfield, $p$ transcendental over $K$, and $\nu \in \mathbb{C}$ with $\beta := p\nu \in K \setminus \{0\}$. Then $1$, $\nu$, $p$ are linearly independent over $K$.
--
--   **Where it sits, and what it does not claim.** In that proof this is the step that prepares Diaz's Corollaire 2 (P)(1) of 2007 for the triple $(\lambda_1,\lambda_2,\lambda_3) = (i\pi, \nu, i\pi)$, with $K = \overline{\mathbb{Q}}$ and $p = i\pi$ (transcendental by Lindemann). Applied there, Diaz's corollary gives $\{(i\pi)\nu, (i\pi)^2\} \not\subset \widetilde{\mathcal{L}}$; since $(i\pi)\nu \in \overline{\mathbb{Q}}$, one gets $\pi^2 \notin \widetilde{\mathcal{L}}$ and hence $e^{\pi^2}$ transcendental, under the hypothesis that some algebraic exponential fibre contains two candidates with $\alpha \notin \mathbb{R}$.
--
--   **That conditional conclusion is *not* what this node asserts.** Diaz's corollary is a deep input with no Mathlib formalisation at this revision, and the augmented logarithm space $\widetilde{\mathcal{L}}$ is not among the mission's definitions. What is recorded here is only the elementary independence step, which is self-contained and needs nothing beyond the transcendence of $p$ over $K$. A contributor who formalises Diaz's Corollaire 2 can compose it with this node to obtain the $e^{\pi^2}$ statement.
--
--   **Proof.** Multiply $A + B\nu + Cp = 0$ by $p$: since $p\nu = \beta$, this reads $Cp^2 + Ap + B\beta = 0$, a quadratic relation for $p$ with all three coefficients in $K$. As $p$ is transcendental over $K$, the polynomial $CX^2 + AX + B\beta \in K[X]$ must be zero, so $C = A = 0$ and $B\beta = 0$; $\beta \neq 0$ then forces $B = 0$.

import Mathlib

open ComplexConjugate

theorem Diaz.indep_of_algebraic_product {K : Subfield ℂ} {p ν : ℂ}
    (hp : Transcendental K p) (hβ : p * ν ∈ K) (hβ0 : p * ν ≠ 0)
    {A B C : ℂ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K)
    (h : A + B * ν + C * p = 0) : A = 0 ∧ B = 0 ∧ C = 0 := by sorry
