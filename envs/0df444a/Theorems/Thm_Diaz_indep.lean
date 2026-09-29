-- Prove2me | Theorems.Thm_Diaz_indep
-- name    : Diaz.indep
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:24.338719+00:00
-- url     : https://prove2.me/theorems/5a10267f-a631-4623-ab76-16d493cfa43a
-- title:
--   $t$ and $\bar t$ are $\mathbb{Q}$-linearly independent
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and $t \in \mathbb{C}$ transcendental over $K$ with $t\bar t \in K$. If $a, b \in \mathbb{Q}$ satisfy
--
--   $$a\,t + b\,\bar t = 0,$$
--
--   then $a = 0$ and $b = 0$.
--
--   **Why.** Transcendence gives $t \neq 0$, and $\bar t = (t\bar t)/t$. Substituting and clearing denominators turns the relation into $a\,t^{2} + b\,(t\bar t) = 0$. If $a \neq 0$ this expresses $t^{2}$ as an element of $K$ times $t \bar t$, hence puts $t^{2}$ — and with it $\bar t^{2} = (t\bar t)^{2}/t^{2}$, hence the cross term $t^{2}+\bar t^{2}$ — inside $K$, which is impossible for transcendental $t$. So $a = 0$, and then $b\,\bar t = 0$ with $\bar t \neq 0$ gives $b = 0$.
--
--   **Role.** This is what makes the coordinate map $(a,b) \mapsto a t + b\bar t$ injective, so that "a function of the coordinates" is a well-defined function on the rational plane. Every statement of the model phrased in coordinates — the norm form, the coordinate action of the involution, the formal exponential $\mathrm{Exp}_0$ — depends on it. It is the model's analogue of the axis lemma.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Model.lean#L106-L140

import Mathlib

open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

theorem Diaz.indep (hT : Transcendental K t) (hρ : t * conj t ∈ K)
    {a b : ℚ} (h : (a : ℂ) * t + (b : ℂ) * conj t = 0) : a = 0 ∧ b = 0 := by sorry
