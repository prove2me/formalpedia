-- Prove2me | Theorems.Thm_Diaz_four_nodes
-- name    : Diaz.four_nodes
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:23:08.481723+00:00
-- url     : https://prove2.me/theorems/8cb6d1f2-9800-4e3a-b501-a8111b3c8aa0
-- title:
--   The reflection circle meets the rational plane in exactly four points
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and $u \in \mathbb{C}$ with $\rho := u\bar u \in K$ and $(u + \bar u)^{2} \notin K$. Let $a, b \in \mathbb{Q}$ and put $v = a u + b \bar u$. If $v$ lies on the same circle as $u$, that is if
--
--   $$v\,\bar v  =  u\,\bar u,$$
--
--   then $(a,b)$ is one of $(1,0)$, $(-1,0)$, $(0,1)$, $(0,-1)$ — in other words $v \in \{\, u,\ -u,\ \bar u,\ -\bar u \,\}$.
--
--   **Why.** Expanding, $v\bar v = (a-b)^{2}\rho + ab\,(u+\bar u)^{2}$. If $ab \neq 0$ the hypothesis lets one solve for $(u+\bar u)^{2}$ as an element of $K$, contradicting $(u+\bar u)^{2} \notin K$; so $ab = 0$. With the cross term gone, the equation reduces to $(a-b)^{2}\rho = \rho$ with $\rho \neq 0$, hence $(a-b)^{2} = 1$, and the four sign cases are exactly the four listed points.
--
--   **Role.** The last of the accompanying note's algebraic statements. The reflection circle through a candidate carries exactly four rational-plane points — the "four nodes" — and the proof is a computation plus a single transcendence input, needing no analysis. That is why it is formalised while the other obstructions of that section of the note are not. The transcendence input $(u+\bar u)^{2} \notin K$ is discharged for an actual candidate in `Diaz.four_nodes_candidate`.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Nodes.lean#L105-L158

import Mathlib

open ComplexConjugate
variable {K : Subfield ℂ} {u : ℂ}

theorem Diaz.four_nodes (hρ : u * conj u ∈ K) (hre : (u + conj u) ^ 2 ∉ K)
    {a b : ℚ} (h : ((a : ℂ) * u + (b : ℂ) * conj u)
      * conj ((a : ℂ) * u + (b : ℂ) * conj u) = u * conj u) :
    (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0)
      ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by sorry
