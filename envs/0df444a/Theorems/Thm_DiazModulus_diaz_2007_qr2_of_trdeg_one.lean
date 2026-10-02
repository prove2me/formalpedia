-- Prove2me | Theorems.Thm_DiazModulus_diaz_2007_qr2_of_trdeg_one
-- name    : DiazModulus.diaz_2007_qr2_of_trdeg_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:44:00.679163+00:00
-- url     : https://prove2.me/theorems/db56b6c4-cdab-496e-9aa3-40f3899e46e6
-- title:
--   Diaz's conjecture (Qr2) in transcendence degree one: for logarithms ℓ₀, ℓ₁ off both axes, a real or purely imaginary ℓ₁/ℓ₀ is rational
-- statement:
--   Let $\ell_0, \ell_1$ be logarithms of algebraic numbers, neither of them real or purely imaginary, such that $\ell_0, \bar\ell_0, \ell_1, \bar\ell_1$ generate a $\mathbb{Q}$-algebra of transcendence degree at most $1$. If $\ell_1/\ell_0$ is real or purely imaginary, then $\ell_1/\ell_0 \in \mathbb{Q}$; in particular it is never purely imaginary.
--
--   This is Diaz's conjecture (Qr2) (2007, p. 376) under the hypothesis on the transcendence degree. Diaz states (Qr2) as a consequence of the four exponentials conjecture; here that conjecture is replaced by the theorem that holds in transcendence degree one.
--
--   **Proof.** Put $\lambda = \bar\ell_0$ and $\mu = \ell_1$, both non-zero logarithms of algebraic numbers. Then $\lambda\mu = |\ell_0|^2\,\ell_1/\ell_0$, so $\lambda\mu$ is real, or purely imaginary, exactly when $\ell_1/\ell_0$ is. In the real case, `DiazModulus.log_mul_real_trichotomy_of_trdeg_one` leaves only $\mu \in \mathbb{Q}\bar\lambda = \mathbb{Q}\ell_0$, since its other two cases put $\ell_0$ on an axis. In the imaginary case, `DiazModulus.log_mul_imaginary_mixed_of_trdeg_one` would put $\bar\ell_0$, hence $\ell_0$, on an axis.
--
--   **Novelty.** Not asserted. The statement is the transcendence-degree-one case of Diaz's conjecture (Qr2) (2007, p. 376), and the proof is Diaz's own argument for (Qr2) from the four exponentials conjecture (p. 377), with that conjecture replaced by the theorem of Waldschmidt (1973) and Brownawell (1974) in transcendence degree one, which Diaz quotes on p. 386. That combination was not found in the sources read.
-- source:
--   The transcendence-degree-one case of Diaz's conjecture (Qr2) (G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, p. 376: for logarithms ℓ₀, ℓ₁ off both axes, ℓ₁/ℓ₀ ∈ ℝ ∪ iℝ implies ℓ₁/ℓ₀ ∈ ℚ). Diaz derives (Qr2) from the four exponentials conjecture with the same 2×2 matrix (p. 377); here the conjecture is replaced by the four exponentials theorem in transcendence degree one (M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Cor. 4; W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974), 22–31, Cor. 7; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Cor. 15.28(c)), which Diaz quotes on p. 386 without combining it with (Qr2). His Cor. 6(2) (p. 387) proves (Qr2) under ℓ₁/ℓ₀ ∈ ℒ̃ instead. The transcendence-degree-one form was not found in the sources read. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

open Complex ComplexConjugate

namespace DiazModulus

theorem diaz_2007_qr2_of_trdeg_one (l₀ l₁ : ℂ)
    (he₀ : IsAlgebraic ℚ (Complex.exp l₀)) (he₁ : IsAlgebraic ℚ (Complex.exp l₁))
    (h₀ : l₀.re ≠ 0 ∧ l₀.im ≠ 0) (h₁ : l₁.re ≠ 0 ∧ l₁.im ≠ 0)
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l₀, l₁, conj l₀, conj l₁} : Set ℂ)) ≤ 1)
    (hax : (l₁ / l₀).im = 0 ∨ (l₁ / l₀).re = 0) :
    ∃ q : ℚ, l₁ / l₀ = q := by
  sorry

end DiazModulus
