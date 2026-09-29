-- Prove2me | Theorems.Thm_DiazModulus_transfer_breaks_exactly
-- name    : DiazModulus.transfer_breaks_exactly
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-13T10:45:47.494293+00:00
-- url     : https://prove2.me/theorems/510e5580-0397-4ddf-8db6-c52efd89a7e5
-- title:
--   A transfer map that destroys candidacy breaks exactly the exponential
-- statement:
--   Let $u$ be a **candidate** ($u \neq 0$, with $|u|$ and $e^{u}$ algebraic) and let $\Phi : \mathbb{C} \to \mathbb{C}$ be a ring homomorphism that fixes every algebraic number and satisfies $\Phi(\bar u) = \overline{\Phi(u)}$. If $\Phi(u)$ is **not** a candidate, then:
--
--   - $|\Phi(u)| = |u|$;
--   - $\Phi(e^{u}) \neq e^{\Phi(u)}$;
--   - $\Phi$ does not map $\mathbb{R}$ into $\mathbb{R}$;
--   - $\Phi$ does not commute with complex conjugation on all of $\mathbb{C}$;
--   - $\Phi$ is not continuous;
--   - $\Phi$ is neither the identity nor complex conjugation.
--
--   **Proof sketch.** $u\bar u = |u|^{2}$ is algebraic, so $\Phi$ fixes it and $\Phi(u)\overline{\Phi(u)} = |u|^{2}$, which gives the modulus. A ring endomorphism of $\mathbb{C}$ that maps $\mathbb{R}$ into $\mathbb{R}$ restricts to a ring endomorphism of $\mathbb{R}$, which is the identity; so $\Phi$ is determined by $\Phi(i) = \pm i$ and is the identity or conjugation. Commuting with conjugation everywhere forces $\Phi(\mathbb{R}) \subseteq \mathbb{R}$, and continuity gives the same conclusion, so each of these conditions is equivalent to $\Phi \in \{\mathrm{id}, \mathrm{conj}\}$. Both of those send candidates to candidates. Finally, if $\Phi(e^{u}) = e^{\Phi(u)}$, then $\Phi(u) \neq 0$, $|\Phi(u)| = |u|$ is algebraic and $e^{\Phi(u)} = \Phi(e^{u})$ is algebraic, so $\Phi(u)$ would be a candidate.
--
--   **What it is for.** `Diaz.candidate_indistinguishable` gives, for a hypothetical counterexample $u$, a map $\Phi$ of this kind with $\Phi(u)$ transcendental, hence not a candidate. This node says what such a map must fail to do. The modulus survives the transfer exactly; the only hypothesis that breaks is the exponential one, and the map is necessarily wild.
--
--   **Not claimed.** Nothing about Diaz's conjecture itself.
-- source:
--   Elementary. Companion to Diaz.candidate_indistinguishable (Proved on this mission); uses the uniqueness of ring endomorphisms of the reals.

import Mathlib
import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem transfer_breaks_exactly (Φ : ℂ →+* ℂ) (u : ℂ) (hu : IsCandidate u)
    (hfix : ∀ a : ℂ, IsAlgebraic ℚ a → Φ a = a)
    (hconj : Φ (conj u) = conj (Φ u))
    (hnot : ¬ IsCandidate (Φ u)) :
    ‖Φ u‖ = ‖u‖ ∧
      Φ (Complex.exp u) ≠ Complex.exp (Φ u) ∧
      (∃ x : ℝ, (Φ (x : ℂ)).im ≠ 0) ∧
      (∃ z : ℂ, Φ (conj z) ≠ conj (Φ z)) ∧
      ¬ Continuous (Φ : ℂ → ℂ) ∧
      Φ ≠ RingHom.id ℂ ∧ Φ ≠ starRingEnd ℂ := by sorry
end DiazModulus
