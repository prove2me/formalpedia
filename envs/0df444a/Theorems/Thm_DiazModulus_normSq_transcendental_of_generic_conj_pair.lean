-- Prove2me | Theorems.Thm_DiazModulus_normSq_transcendental_of_generic_conj_pair
-- name    : DiazModulus.normSq_transcendental_of_generic_conj_pair
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T03:15:46.018644+00:00
-- url     : https://prove2.me/theorems/271a4c35-09ec-43c2-98f1-2275076c25df
-- title:
--   Transcendence of $|u|^{2}=\Re(u)^{2}+\Im(u)^{2}$ for a generic conjugate pair
-- statement:
--   Let $u\in\mathbb C$ be such that both $e^{u}$ and $e^{ar u}$ are algebraic, with $\Re(u)
--   e 0$, $\Im(u)
--   e 0$, and with $\Re(u)$, $\Im(u)$ and the ratio $\Re(u)/\Im(u)$ all transcendental. Then the squared modulus is transcendental:
--
--   $$\Re(u)^{2}+\Im(u)^{2}\ 	ext{is transcendental over }\mathbb Q.$$
--
--   This is the substantive form of Diaz's modulus statement for a generic conjugate pair. It is phrased for $|u|^{2}$ rather than for $|u|$ because the squared modulus is the polynomial quantity $\Re(u)^{2}+\Im(u)^{2}$ in the real and imaginary parts, which is the shape the transcendence argument actually works with; the two coordinates and their ratio appear in the hypotheses in exactly that form.
--
--   The passage from this statement to the transcendence of $|u|$ itself is elementary and is performed in the reduction: if $|u|$ were algebraic then so would be $|u|^{2}$, since algebraic numbers are closed under squaring.
-- source:
--   G. Diaz, modulus conjecture: if $|u|$ is algebraic then $e^{u}$ is transcendental. This lemma is the squared-modulus form of the conclusion; the passage from $|u|^{2}$ to $|u|$ is elementary and is carried out in the reduction.

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem normSq_transcendental_of_generic_conj_pair :
    ∀ u : ℂ,
      IsAlgebraic ℚ (Complex.exp u) →
      IsAlgebraic ℚ (Complex.exp ((starRingEnd ℂ) u)) →
      u.re ≠ 0 → u.im ≠ 0 →
      Transcendental ℚ ((u.re : ℝ) : ℂ) →
      Transcendental ℚ ((u.im : ℝ) : ℂ) →
      Transcendental ℚ ((u.re / u.im : ℝ) : ℂ) →
      Transcendental ℚ (((u.re ^ 2 + u.im ^ 2 : ℝ)) : ℂ) := by sorry

end DiazModulus
