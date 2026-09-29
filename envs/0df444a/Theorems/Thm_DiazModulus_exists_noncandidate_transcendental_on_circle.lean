-- Prove2me | Theorems.Thm_DiazModulus_exists_noncandidate_transcendental_on_circle
-- name    : DiazModulus.exists_noncandidate_transcendental_on_circle
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-24T04:56:41.324987+00:00
-- url     : https://prove2.me/theorems/d08bcf37-eb9f-4285-9ff0-4114280c0dce
-- title:
--   Every circle of positive radius contains a point t transcendental over a given countable field, with e^t transcendental
-- statement:
--   **Non-candidates on every circle.**
--
--   Let $K \subseteq \mathbb{C}$ be a countable subfield and $\rho > 0$ real. Then some $t$ with $t\bar t = \rho$ is transcendental over $K$ and has $e^{t}$ transcendental.
--
--   The circle is uncountable, while the numbers algebraic over $K$ and the numbers $z$ with $e^{z}$ algebraic form countable sets.
--
--   This replaces an explicit choice such as $t = re^{i}$ on the circle of radius $r$. That choice needs $e^{i}$ to be transcendental over $K$, which is known for $K = \overline{\mathbb{Q}}$ but not once $\pi \in K$. It also leaves open whether $e^{t}$ is algebraic, which is an instance of Diaz's conjecture.
--
--   **Novelty.** None claimed. Routine.
-- source:
--   Carlo Perassi, companion note to https://github.com/carlok/diaz-modulus-lean, version 1.9, 25 September 2026 (GitHub release note-v1.9), Section 5, the paragraph after Theorem 5.1 (here over any countable base field). Novelty is not asserted. Formal proof: Diaz modulus mission, 24 September 2026 (C. Perassi).

import Mathlib

open ComplexConjugate

namespace DiazModulus

theorem exists_noncandidate_transcendental_on_circle (K : Subfield ℂ) (hK : Countable ↥K)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ t : ℂ, t * conj t = (ρ : ℂ) ∧ Transcendental (↥K) t ∧
      Transcendental ℚ (Complex.exp t) := by sorry

end DiazModulus
