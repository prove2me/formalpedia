-- Prove2me | Theorems.Thm_Diaz_norm_mem_iff
-- name    : Diaz.norm_mem_iff
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:19.359449+00:00
-- url     : https://prove2.me/theorems/dde35154-562b-49fb-8068-cc2077ce5402
-- title:
--   The rational plane: $x\bar x \in K$ exactly on the two coordinate rays
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a subfield and let $t \in \mathbb{C}$ be transcendental over $K$ with $\rho := t\bar t \in K$. For rationals $a, b$ put $x = a t + b\bar t$. Then
--
--   $$x\,\bar x \in K \qquad\Longleftrightarrow\qquad a = 0 \ \text{ or } \ b = 0.$$
--
--   **Why.** Expanding, $x\bar x = (a^{2}+b^{2})\,\rho + ab\,(t^{2} + \bar t^{2})$. The first summand always lies in $K$, so $x\bar x \in K$ forces $ab\,(t^{2}+\bar t^{2}) \in K$; if $ab \neq 0$ this puts the cross term $t^{2} + \bar t^{2}$ into $K$, and then $t$ is a root of $X^{4} - (t^2+\bar t^2) X^{2} + \rho^{2}$ over $K$, contradicting transcendence. Conversely, if $a = 0$ or $b = 0$ the cross term drops out and $x\bar x = (a^{2}+b^{2})\rho \in K$.
--
--   **Role.** This is the characterisation of the set $\mathcal{D}_0$ in the model. Take $t$ transcendental over $K$ lying on the circle $z\bar z = \rho$: it satisfies $\bar t = \rho/t$, exactly as the formal involution $\sigma T = \rho/T$ of the Laurent model does, and the plane it spans with $\bar t$ carries the same norm form. The theorem says the elements of that plane with "algebraic modulus" are precisely the rational multiples of $t$ and of $\bar t$ — two rays, and in particular non-zero ones exist. So every purely algebraic constraint a Diaz candidate satisfies is satisfied here too, by an ordinary complex number that is *not* a candidate; the single thing $t$ lacks is that $e^{t}$ be algebraic, and that is precisely the input no algebraic argument can reach.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Model.lean#L70-L104

import Mathlib

open ComplexConjugate
open Polynomial
variable {K : Subfield ℂ} {t : ℂ}

theorem Diaz.norm_mem_iff (hT : Transcendental K t) (hρ : t * conj t ∈ K) (a b : ℚ) :
    ((a : ℂ) * t + (b : ℂ) * conj t) * conj ((a : ℂ) * t + (b : ℂ) * conj t) ∈ K
      ↔ a = 0 ∨ b = 0 := by sorry
