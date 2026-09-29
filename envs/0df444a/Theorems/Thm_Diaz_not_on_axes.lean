-- Prove2me | Theorems.Thm_Diaz_not_on_axes
-- name    : Diaz.not_on_axes
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:00.943388+00:00
-- url     : https://prove2.me/theorems/229a0075-d952-42b0-a1b2-ff6d45f9a91d
-- title:
--   The axis lemma: a candidate is neither real nor purely imaginary
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and let $u \in \mathbb{C}$ be transcendental over $K$ with $u\bar u \in K$. Then
--
--   $$\bar u \neq u \qquad\text{and}\qquad \bar u \neq -u .$$
--
--   **Why.** In either case $u^{2}$ would land in $K$: if $\bar u = u$ then $u^{2} = u\bar u \in K$; if $\bar u = -u$ then $u\bar u = -u^{2}$, so $u^{2} = -(u\bar u) \in K$. But $u^{2} \in K$ makes $u$ a root of $X^{2} - u^{2}$ over $K$, contradicting transcendence.
--
--   **Role.** Geometrically: $u$ lies on neither the real nor the imaginary axis. This is the input the four-node theorem needs in order to know that $u + \bar u \neq 0$ — that a candidate has a non-zero real part — and hence that $(u+\bar u)^{2}$ is a legitimate object to argue about. In the accompanying note this is the axis lemma; here it is derived rather than assumed, which is what lets the four-node statement be stated with arithmetic hypotheses only.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Nodes.lean#L23-L44

import Mathlib

open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

theorem Diaz.not_on_axes (hT : Transcendental K u) (hρ : u * conj u ∈ K) :
    conj u ≠ u ∧ conj u ≠ -u := by sorry
