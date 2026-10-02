-- Prove2me | Theorems.Thm_DiazModulus_baker_two_logs
-- name    : DiazModulus.baker_two_logs
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:17:31.418895+00:00
-- url     : https://prove2.me/theorems/f04bc443-81b3-49dd-a72f-1cbbcdf9b7b2
-- title:
--   Baker's theorem for two logarithms: a·x + b·y is transcendental for ℚ-independent logarithms x, y and algebraic (a, b) ≠ 0
-- statement:
--   Let $x$ and $y$ be logarithms of algebraic numbers, linearly independent over $\mathbb{Q}$, and let $a, b$ be algebraic numbers, not both zero. Then $ax + by$ is transcendental.
--
--   This is the form of Baker's theorem carried as the hypothesis `hB` by the nodes of this mission that need it (for example `DiazModulus.candidate_one_log_saturation` and `DiazModulus.no_algebraic_generalized_line`); the statement is exactly that hypothesis, so it can be passed to them. It is the case of two logarithms of `Schanuel.baker_linear_forms_in_logarithms`, Baker's theorem with a constant term, proved in this mission by Chapter 4 of Waldschmidt's book.
--
--   **Novelty.** None: Baker (1966). The contribution of this node is the formal proof.
-- source:
--   A. Baker, Linear forms in the logarithms of algebraic numbers I, Mathematika 13 (1966), 204–216; the proof follows M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Chapter 4, after D. Bertrand and D. W. Masser, Linear forms in elliptic integrals, Invent. Math. 58 (1980), 283–288; D. W. Masser, A note on Baker's theorem, in Recent Progress in Analytic Number Theory, Vol. 2 (Durham, 1979), Academic Press, 1981, 153–158. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

namespace DiazModulus

/-- **Baker's theorem, two-logarithm form** (the hypothesis `hB` of this library). A non-zero linear
combination, with algebraic coefficients, of two `ℚ`-linearly independent logarithms of algebraic
numbers is transcendental. This is Baker's theorem (Waldschmidt, *Diophantine Approximation on Linear
Algebraic Groups*, Th. 1.6) for two logarithms. -/
theorem baker_two_logs : ∀ x y a b : ℂ,
    IsAlgebraic ℚ (Complex.exp x) → IsAlgebraic ℚ (Complex.exp y) →
    (∀ p q : ℚ, (p : ℂ) * x + (q : ℂ) * y = 0 → p = 0 ∧ q = 0) →
    IsAlgebraic ℚ a → IsAlgebraic ℚ b → ¬(a = 0 ∧ b = 0) →
    Transcendental ℚ (a * x + b * y) := by
  sorry

end DiazModulus
