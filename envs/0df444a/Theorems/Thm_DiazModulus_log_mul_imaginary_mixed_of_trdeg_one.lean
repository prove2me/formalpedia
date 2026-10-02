-- Prove2me | Theorems.Thm_DiazModulus_log_mul_imaginary_mixed_of_trdeg_one
-- name    : DiazModulus.log_mul_imaginary_mixed_of_trdeg_one
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-02T08:44:01.753533+00:00
-- url     : https://prove2.me/theorems/f5946b27-bd72-4cda-b34d-bf55accefdd3
-- title:
--   In transcendence degree one, a purely imaginary product of two non-zero logarithms has one real and one purely imaginary factor
-- statement:
--   Let $\lambda, \mu$ be non-zero logarithms of algebraic numbers such that $\lambda, \bar\lambda, \mu, \bar\mu$ generate a $\mathbb{Q}$-algebra of transcendence degree at most $1$. If $\lambda\mu$ is purely imaginary, then one of $\lambda, \mu$ is real and the other purely imaginary.
--
--   The product need not be algebraic. Together with `DiazModulus.log_mul_real_trichotomy_of_trdeg_one` it describes every product of two such logarithms that lies on an axis.
--
--   **Proof.** The matrix $\begin{pmatrix}\lambda & \bar\lambda\\ -\bar\mu & \mu\end{pmatrix}$ has non-zero logarithms of algebraic numbers as entries ($-\bar\mu$ is a logarithm of $1/\overline{e^{\mu}}$), its entries lie in the same $\mathbb{Q}$-algebra, and its determinant $\lambda\mu + \overline{\lambda\mu} = 2\,\mathrm{Re}(\lambda\mu)$ vanishes. By `DiazModulus.four_exponentials_trdeg_one` its rows or its columns are linearly dependent over $\mathbb{Q}$. Dependent rows, $a\lambda - b\bar\mu = 0$ and $a\bar\lambda + b\mu = 0$, give $2b\mu = 0$ once the first is conjugated, so $b = 0$ and then $a\lambda = 0$, which is impossible. Dependent columns give $a\lambda + b\bar\lambda = 0$ and $b\mu - a\bar\mu = 0$; on real and imaginary parts they put $\lambda$ and $\mu$ on different axes.
--
--   **Novelty.** Not asserted. The statement is the transcendence-degree-one case of Diaz's conjecture (Qr2) (2007, p. 376), and the proof is Diaz's own argument for (Qr2) from the four exponentials conjecture (p. 377), with that conjecture replaced by the theorem of Waldschmidt (1973) and Brownawell (1974) in transcendence degree one, which Diaz quotes on p. 386. That combination was not found in the sources read.
-- source:
--   The transcendence-degree-one case of Diaz's conjecture (Qr2) (G. Diaz, Produits et quotients de combinaisons linéaires de logarithmes de nombres algébriques : conjectures et résultats partiels, J. Théor. Nombres Bordeaux 19 (2007), 373–391, p. 376: for logarithms ℓ₀, ℓ₁ off both axes, ℓ₁/ℓ₀ ∈ ℝ ∪ iℝ implies ℓ₁/ℓ₀ ∈ ℚ). Diaz derives (Qr2) from the four exponentials conjecture with the same 2×2 matrix (p. 377); here the conjecture is replaced by the four exponentials theorem in transcendence degree one (M. Waldschmidt, Solution du huitième problème de Schneider, J. Number Theory 5 (1973), 191–202, Cor. 4; W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974), 22–31, Cor. 7; M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Cor. 15.28(c)), which Diaz quotes on p. 386 without combining it with (Qr2). His Cor. 6(2) (p. 387) proves (Qr2) under ℓ₁/ℓ₀ ∈ ℒ̃ instead. The transcendence-degree-one form was not found in the sources read. Formal proof: Diaz modulus mission, 2 October 2026 (C. Perassi).

import Mathlib

open Complex ComplexConjugate

namespace DiazModulus

theorem log_mul_imaginary_mixed_of_trdeg_one (l m : ℂ) (hl : l ≠ 0) (hm : m ≠ 0)
    (hel : IsAlgebraic ℚ (Complex.exp l)) (hem : IsAlgebraic ℚ (Complex.exp m))
    (htr : Algebra.trdeg ℚ ↥(Algebra.adjoin ℚ ({l, m, conj l, conj m} : Set ℂ)) ≤ 1)
    (himag : (l * m).re = 0) :
    (l.im = 0 ∧ m.re = 0) ∨ (l.re = 0 ∧ m.im = 0) := by
  sorry

end DiazModulus
