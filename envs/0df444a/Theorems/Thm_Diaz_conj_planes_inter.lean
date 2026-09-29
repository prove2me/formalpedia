-- Prove2me | Theorems.Thm_Diaz_conj_planes_inter
-- name    : Diaz.conj_planes_inter
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:18:06.831903+00:00
-- url     : https://prove2.me/theorems/6c04c573-aa4f-43dc-a931-ea315ebfcec5
-- title:
--   The two conjugate planes meet only in the base field
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield, $u$ transcendental over $K$ with $u\bar u \in K$, and $A,B,C,D \in K$. If $A + Bu = C + D\bar u$, then $B = D = 0$ and $A = C$.
--
--   Equivalently: $(K \oplus Ku) \cap (K \oplus K\bar u) = K$, so every non-algebraic element of $U_+ \cup U_-$ has a unique chirality.
--
--   **Where this sits.** This is the first sentence of the proof of Carlo Perassi's chiral multiplication law: "The intersection $U_+ \cap U_- = \bar{\mathbb{Q}}$ by the independence of $1, u, \bar u$, so every nonalgebraic element has a unique chirality."
--
--   **Proof.** The relation says $(A-C) + Bu + (-D)\bar u = 0$. Multiplying by $u$ and using $\bar u = \rho/u$ with $\rho = u\bar u \in K$ turns it into $Bu^{2} + (A-C)u + (-D\rho) = 0$, a polynomial relation for $u$ over $K$. Transcendence forces that polynomial to be zero, so $B = 0$ and $A = C$; the original relation then reads $D\bar u = 0$, and $\bar u \neq 0$.
--
--   This is a corollary of the independence of $1, u, \bar u$ over $K$, which is already on the mission as `Diaz.indep_three`; it is recorded separately because the chiral multiplication law is stated in terms of the two planes rather than of a linear relation, and because the chirality statement is what his product filter consumes.
--
--   **What is deliberately not claimed.** The equivalence of the chiral multiplication law — that $xy \in \widetilde{\mathcal{L}}$ exactly when $x$ and $y$ lie in opposite planes — needs the saturation of the two conjugate planes and hence Roy's strong six exponentials theorem, and is not asserted.
--
--   Elementary. Novelty is not asserted.
--
--   **Source.** Carlo Perassi, unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.conj_planes_inter {K : Subfield ℂ} {u : ℂ}
    (hT : Transcendental (↥K) u) (hρ : u * conj u ∈ K)
    {A B C D : ℂ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K) (hD : D ∈ K)
    (h : A + B * u = C + D * conj u) : B = 0 ∧ D = 0 ∧ A = C := by sorry
