-- Prove2me | Theorems.Thm_Diaz_conj_planes_mul
-- name    : Diaz.conj_planes_mul
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-08T07:18:07.340854+00:00
-- url     : https://prove2.me/theorems/8fdabc03-d389-4fc1-af77-aa927e0ea29e
-- title:
--   Opposite conjugate planes multiply into the span of 1, u and its conjugate
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and $u \in \mathbb{C}$ with $\rho = u\bar u \in K$. For $A,B,C,D \in K$ the product
--
--   $$(A + Bu)(C + D\bar u) = (AC + BD\rho) + (BC)u + (AD)\bar u$$
--
--   lies in $K + Ku + K\bar u$.
--
--   **Where this sits.** This is the elementary half of Carlo Perassi's theorem on two saturated conjugate planes, whose case $x = u$ is Theorem 6.4 of his companion note to https://github.com/carlok/diaz-modulus-lean (version 1.9, 25 September 2026, GitHub release note-v1.9): the computation
--
--   $$x(C + D\bar u) = AC + BD q + BC u + AD \bar u \in \widetilde{\mathcal{L}}$$
--
--   establishing $U_- \subseteq \mathcal{M}_x$ for $x = A + Bu \in U_+$, where $U_\pm = \bar{\mathbb{Q}} \oplus \bar{\mathbb{Q}}u^{\pm}$ and $\widetilde{\mathcal{L}} = \bar{\mathbb{Q}} + \operatorname{span}_{\bar{\mathbb{Q}}}\mathcal{L}$. With $K = \bar{\mathbb{Q}}$ and $u$ a Diaz candidate, the right-hand side is exactly a member of $\widetilde{\mathcal{L}}$, since $u$ and $\bar u$ are logarithms.
--
--   The one thing that makes the identity work is $u \cdot \bar u \in K$: the product of the two "opposite" generators stays in the base. This is the whole content of the chirality in his chiral multiplication law.
--
--   **What is deliberately not claimed.** The reverse inclusion $\mathcal{M}_x \subseteq U_-$ is the multiplier bound $\dim_{\bar{\mathbb{Q}}}\mathcal{M}_x \le 2$, which is Roy's strong six exponentials theorem and is not available in Mathlib. Without it the saturation — the equality $\mathcal{M}_x = U_-$ — is not asserted, and neither is the "only if" half of the chiral multiplication law.
--
--   Elementary. Novelty is not asserted.
--
--   **Source.** Carlo Perassi; in this generality unpublished apart from this node. The mathematics is his; this node only records one step of it in Lean, and claims no novelty of its own.

import Mathlib
import Definitions.Def_Diaz_Closure
import Definitions.Def_Diaz_Instantiation

open ComplexConjugate
open Diaz

theorem Diaz.conj_planes_mul {K : Subfield ℂ} {u : ℂ} (hρ : u * conj u ∈ K)
    {A B C D : ℂ} (hA : A ∈ K) (hB : B ∈ K) (hC : C ∈ K) (hD : D ∈ K) :
    ∃ p q r : ℂ, p ∈ K ∧ q ∈ K ∧ r ∈ K ∧
      (A + B * u) * (C + D * conj u) = p + q * u + r * conj u := by sorry
