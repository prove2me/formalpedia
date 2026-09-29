-- Prove2me | Theorems.Thm_Diaz_Hmat_transfer
-- name    : Diaz.Hmat_transfer
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T08:22:53.600203+00:00
-- url     : https://prove2.me/theorems/f996238a-a3bd-4825-afbf-200909a27d61
-- title:
--   $\Phi$ carries $H(u,r)$ to $H(t,r)$ when it fixes $r$ and sends $u$ to $t$
-- statement:
--   Let $K \subseteq \mathbb{C}$ be a conjugation-stable subfield, $r \in K$, and let $u, t \in \mathbb{C}$ be non-zero with $\rho := u\bar u \in K$ and $t\bar t = u\bar u$. Let $\Phi : \mathbb{C} \to \mathbb{C}$ be a ring homomorphism fixing $K$ pointwise with $\Phi(u) = t$. Then, applying $\Phi$ entrywise,
--
--   $$H(u,r)^{\Phi}  =  H(t,r), \qquad\text{where } H(x,r) = \begin{pmatrix} x & r \\ r & \bar x \end{pmatrix}.$$
--
--   **Why.** Three of the four entries are immediate: $\Phi(u) = t$ by hypothesis and $\Phi(r) = r$ because $r \in K$. The fourth is the whole point — $\Phi(\bar u) = \bar t$ — and it is not an extra assumption but a consequence of `Diaz.conj_comm` applied at $z = u$, which lies in the hull $K(u)$.
--
--   **Role.** Together with `Diaz.coeff_transfer` this closes the transfer argument for the rank-one matrix: the matrix attached to a candidate is carried onto the matrix attached to an ordinary complex number of the same modulus. Every statement about $H$ expressible in terms of ranks, structural ranks over $K$, or vanishing coefficients therefore holds for the candidate exactly when it holds in the model.
-- source:
--   https://github.com/carlok/diaz-modulus-lean/blob/801802b8ac052dff50baf17ac4a7ceac3e994ca9/Diaz/Transfer.lean#L81-L92

import Mathlib
import Definitions.Def_Diaz_Rigidity

open ComplexConjugate
open Diaz
variable {K : Subfield ℂ} {u t : ℂ}

theorem Diaz.Hmat_transfer (Φ : ℂ →+* ℂ) (hK : ∀ a ∈ K, Φ a = a) {r : ℂ} (hr : r ∈ K)
    (hKconj : ∀ a ∈ K, conj a ∈ K) (hu0 : u ≠ 0) (ht0 : t ≠ 0) (hΦu : Φ u = t)
    (hρ : u * conj u ∈ K) (hρt : t * conj t = u * conj u) :
    (Hmat u r).map Φ = Hmat t r := by sorry
