-- Prove2me | Theorems.Thm_DiazModulus_generic_indistinguishable_over_pi
-- name    : DiazModulus.generic_indistinguishable_over_pi
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T05:05:14.000361+00:00
-- url     : https://prove2.me/theorems/7f17cb28-2090-43c8-9cc0-a878aac8a1d9
-- title:
--   A point transcendental over the algebraic closure K of ℚ(π), on a circle of algebraic radius, is indistinguishable over K from a non-candidate
-- statement:
--   **Indistinguishability that also fixes $\pi$.**
--
--   Let $K$ be the algebraic closure of $\mathbb{Q}(\pi)$ in $\mathbb{C}$, and let $u$ be transcendental over $K$ with $|u|^{2}$ algebraic. Then there are a point $t$ of the same circle, transcendental over $K$, with $e^{t}$ transcendental, and a ring homomorphism $\Phi : \mathbb{C} \to \mathbb{C}$ fixing $K$ pointwise with $\Phi(u) = t$. $\Phi$ commutes with complex conjugation on $K(u)$ and maps $K(u)$ into $K(t)$. For every matrix $N$ over $K(u)$ and all vectors $w$, $v$ over $K$,
--
--   $$w^{T} N v = 0 \iff w^{T}\, \Phi(N)\, v = 0.$$
--
--   So for a candidate transcendental over $K$, which means a candidate algebraically independent of $\pi$, no vanishing statement with coefficients algebraic over $\mathbb{Q}(\pi)$ about a matrix over $K(u)$ separates $u$ from a point of its circle that is not a candidate. `Diaz.candidate_indistinguishable_by_coeff` says the same over $\overline{\mathbb{Q}}$, where $\Phi$ need not fix $\pi$. The hypothesis cannot be dropped: if $u \in K$, then $\Phi$ fixes $u$.
--
--   **Novelty.** None claimed.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Theorem 5.2. Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Definitions.Def_Diaz_Closure

open ComplexConjugate

namespace DiazModulus

theorem generic_indistinguishable_over_pi (K : Subfield ℂ)
    (hK : ∀ z : ℂ, z ∈ K ↔
      IsAlgebraic (↥(IntermediateField.adjoin ℚ ({((Real.pi : ℝ) : ℂ)} : Set ℂ))) z)
    {u : ℂ} (hu0 : u ≠ 0) (hρ : IsAlgebraic ℚ (u * conj u)) (hgen : Transcendental (↥K) u) :
    ∃ t : ℂ, t ≠ 0 ∧ Transcendental (↥K) t ∧ t * conj t = u * conj u ∧
      Transcendental ℚ (Complex.exp t) ∧
      ∃ Φ : ℂ →+* ℂ, (∀ a ∈ K, Φ a = a) ∧ Φ u = t ∧
        (∀ z ∈ Diaz.hull K u, Φ (conj z) = conj (Φ z)) ∧
        (∀ z ∈ Diaz.hull K u, Φ z ∈ Diaz.hull K t) ∧
        ∀ (p q : ℕ) (N : Matrix (Fin p) (Fin q) ℂ) (w : Fin p → ℂ) (v : Fin q → ℂ),
          (∀ i j, N i j ∈ Diaz.hull K u) → (∀ i, w i ∈ K) → (∀ j, v j ∈ K) →
            ((∑ i, ∑ j, w i * N i j * v j) = 0 ↔ (∑ i, ∑ j, w i * Φ (N i j) * v j) = 0) := by
  sorry

end DiazModulus
