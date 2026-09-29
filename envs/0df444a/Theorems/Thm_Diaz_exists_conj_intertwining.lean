-- Prove2me | Theorems.Thm_Diaz_exists_conj_intertwining
-- name    : Diaz.exists_conj_intertwining
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:55.270501+00:00
-- url     : https://prove2.me/theorems/55b6e9a4-5357-482b-82d0-eae88a18a1ac
-- title:
--   The closure theorem with existence: two transcendental points of one circle are carried onto each other
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a conjugation-stable subfield and let $u, t \in \mathbb{C}$ both be transcendental over $K$, with
--
--   $$\rho := u\bar u \in K \qquad\text{and}\qquad t\,\bar t = u\,\bar u .$$
--
--   Then there exists a ring homomorphism $\Phi : \mathbb{C} \to \mathbb{C}$ with
--
--   $$\Phi|_{K} = \mathrm{id}_{K}, \qquad \Phi(u) = t, \qquad \text{and} \qquad \forall\, z \in K(u),\ \ \Phi(\bar z) = \overline{\Phi(z)} .$$
--
--   **Why.** Existence of a $\Phi$ fixing $K$ and sending $u \mapsto t$ is the Steinitz extension statement `Diaz.exists_ringHom_of_transcendental`, available because both points are transcendental over $K$. That $\Phi$ then intertwines conjugation on the hull is *not an additional requirement*: it follows from `Diaz.conj_comm`, because $\bar u = \rho/u$ makes conjugation a rational function of the generator over $K$.
--
--   **Role.** This is the closure theorem in its unconditional form, and the mathematical heart of the negative result. Take $u$ to be a hypothetical counterexample to Diaz's modulus conjecture and $t$ an ordinary transcendental point of the same circle. The theorem produces an embedding of the ambient field into itself that fixes the base, matches the two points, and respects the involution — so no invariant built from the field structure of $K(u)$ together with complex conjugation can tell $u$ from $t$. Since $t$ is not a counterexample, no such invariant can certify that $u$ is one, and a whole class of algebraic proof strategies is ruled out.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Transfer.lean#L99-L112

import Mathlib
import Definitions.Def_Diaz_Closure

open ComplexConjugate
open Diaz
variable {K : Subfield ℂ} {u t : ℂ}

theorem Diaz.exists_conj_intertwining (hKconj : ∀ a ∈ K, conj a ∈ K)
    (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t
      ∧ ∀ z ∈ hull K u, Φ (conj z) = conj (Φ z) := by sorry
