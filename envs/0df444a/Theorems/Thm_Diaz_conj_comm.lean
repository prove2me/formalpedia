-- Prove2me | Theorems.Thm_Diaz_conj_comm
-- name    : Diaz.conj_comm
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:53.119446+00:00
-- url     : https://prove2.me/theorems/7e12af51-a66c-43a0-bf1f-5b612530560b
-- title:
--   An isomorphism matching the generators automatically intertwines complex conjugation
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a conjugation-stable subfield, let $u, t \in \mathbb{C}$ be non-zero, and let $\Phi : \mathbb{C} \to \mathbb{C}$ be a ring homomorphism with
--
--   $$\Phi|_{K} = \mathrm{id}_{K}, \qquad \Phi(u) = t, \qquad \rho := u\bar u \in K, \qquad t\,\bar t = u\,\bar u .$$
--
--   Then $\Phi$ commutes with complex conjugation on the whole hull $K(u)$:
--
--   $$\forall\, z \in K(u), \qquad \Phi(\bar z) = \overline{\Phi(z)}.$$
--
--   **Why.** The two ring homomorphisms $\Phi \circ (\bar{\cdot})$ and $(\bar{\cdot}) \circ \Phi$ agree on $K$ (which is conjugation-stable and fixed by $\Phi$) and at the generator $u$: there $\Phi(\bar u) = \Phi(\rho/u) = \rho/t$ and $\overline{\Phi(u)} = \bar t = \rho/t$, using $t\bar t = \rho$. By the rigidity lemma `Diaz.eqOn_hull`, two ring homomorphisms agreeing on $K$ and at $u$ agree on all of $K(u)$.
--
--   **Role.** This is the content of the closure theorem, and the point at which an earlier draft of the accompanying note went wrong. The intertwining is **not arranged**: it is forced, because $\bar u = \rho/u$ makes conjugation a rational function of the generator over $K$ rather than extra structure that a map might fail to respect. Consequently a proof strategy that hopes to separate a candidate from an ordinary point of the same circle by exhibiting some conjugation-sensitive invariant cannot succeed — the invariant transfers.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Transfer.lean#L36-L64

import Mathlib
import Definitions.Def_Diaz_Closure

open ComplexConjugate
open Diaz
variable {K : Subfield ℂ} {u t : ℂ}

theorem Diaz.conj_comm (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a)
    (hKconj : ∀ a ∈ K, conj a ∈ K)
    (hu0 : u ≠ 0) (ht0 : t ≠ 0) (hΦu : Φ u = t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    ∀ z ∈ hull K u, Φ (conj z) = conj (Φ z) := by sorry
