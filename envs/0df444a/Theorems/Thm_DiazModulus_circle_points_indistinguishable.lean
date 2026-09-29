-- Prove2me | Theorems.Thm_DiazModulus_circle_points_indistinguishable
-- name    : DiazModulus.circle_points_indistinguishable
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T04:56:55.452676+00:00
-- url     : https://prove2.me/theorems/cb21e2da-fd62-4996-8044-92475b014747
-- title:
--   Two points of a circle that are transcendental over a conjugation-stable field K containing the squared radius are indistinguishable over K
-- statement:
--   **Indistinguishability over a conjugation-stable base field.**
--
--   Let $K \subseteq \mathbb{C}$ be a subfield stable under complex conjugation, and let $u$, $t$ be transcendental over $K$ with $t\bar t = u\bar u \in K$. Then there is a ring homomorphism $\Phi : \mathbb{C} \to \mathbb{C}$ fixing $K$ pointwise, with $\Phi(u) = t$, which commutes with complex conjugation on $K(u)$ and maps $K(u)$ into $K(t)$. For every matrix $N$ over $K(u)$ and all vectors $w$, $v$ over $K$,
--
--   $$w^{T} N v = 0 \iff w^{T}\, \Phi(N)\, v = 0.$$
--
--   The transfer in `Diaz.candidate_indistinguishable_by_coeff` is the case $K = \overline{\mathbb{Q}}$, for one particular $t$. A larger $K$ makes $\Phi$ fix more: with $K$ the algebraic closure of $\mathbb{Q}(\pi)$, $\Phi$ fixes $\pi$ (`DiazModulus.generic_indistinguishable_over_pi`).
--
--   **Novelty.** None claimed. Routine from `Diaz.exists_ringHom_of_transcendental`.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), the argument of Theorems 5.1 and 5.2 over a conjugation-stable base field (Appendix A lists this node with Theorem 5.2). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_Diaz_Closure

open ComplexConjugate

namespace DiazModulus

theorem circle_points_indistinguishable (K : Subfield ℂ) (hKc : ∀ z ∈ K, conj z ∈ K)
    {u t : ℂ} (hρ : u * conj u ∈ K) (hu : Transcendental (↥K) u) (ht : Transcendental (↥K) t)
    (hut : t * conj t = u * conj u) :
    ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t ∧
      (∀ z ∈ Diaz.hull K u, Φ (conj z) = conj (Φ z)) ∧
      (∀ z ∈ Diaz.hull K u, Φ z ∈ Diaz.hull K t) ∧
      ∀ (p q : ℕ) (N : Matrix (Fin p) (Fin q) ℂ) (w : Fin p → ℂ) (v : Fin q → ℂ),
        (∀ i j, N i j ∈ Diaz.hull K u) → (∀ i, w i ∈ K) → (∀ j, v j ∈ K) →
          ((∑ i, ∑ j, w i * N i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (N i j) * v j) = 0) := by
  sorry

end DiazModulus
