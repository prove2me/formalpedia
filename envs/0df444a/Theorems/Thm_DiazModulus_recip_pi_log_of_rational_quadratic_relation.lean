-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_log_of_rational_quadratic_relation
-- name    : DiazModulus.recip_pi_log_of_rational_quadratic_relation
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-04T18:33:09.597343+00:00
-- url     : https://prove2.me/theorems/de445e9d-80c9-4aef-864b-71b412e9ea1a
-- title:
--   If a·t² + b·π² is rational for a real logarithm t ≠ 0 of an algebraic number, with a ≠ 0 and b rational, then e^{iγ/π} is transcendental for every rational γ ≠ 0
-- statement:
--   Let $t \neq 0$ be real with $e^t$ algebraic, and let $a, b, c \in \mathbb{Q}$ with $a \neq 0$ and $a t^2 + b\pi^2 = c$. Then $e^{i\gamma/\pi}$ is transcendental for every $\gamma \in \mathbb{Q}^\times$.
--
--   The case $a = b = 1$ is `DiazModulus.recip_pi_log_of_torsion_rational_modulus`. The hypothesis cannot hold when $b = 0$, since $t$ would then be algebraic, against Hermite–Lindemann; the proof needs no case split. With $t = \log 2$, $a = -1/2$ and $b = 1/12$ it gives `DiazModulus.dilog_half_irrational_or_exp_i_div_pi_transcendental`.
--
--   **Proof.** Suppose $e^{i\gamma/\pi}$ is algebraic, so that $\lambda = i\gamma/\pi$ is a logarithm of an algebraic number. The relation gives $t^2/(i\pi) = -\frac{c}{a\gamma}\,\lambda + \frac{b}{a}\, i\pi$, a rational combination of the logarithms $\lambda$ and $i\pi$, hence again a logarithm of an algebraic number. The matrix $\begin{pmatrix} t & t^2/(i\pi) \\ i\pi & t\end{pmatrix}$ has determinant $0$, and its entries lie in a field of transcendence degree one, since $t$ is algebraic over $\mathbb{Q}(\pi)$. By the four exponentials theorem in transcendence degree one (`DiazModulus.four_exponentials_trdeg_one`), its rows or its columns are linearly dependent over $\mathbb{Q}$. Either way $\alpha t + \beta\, i\pi = 0$ with $\alpha, \beta \in \mathbb{Q}$ not both zero, which is impossible because $t$ is real and non-zero and $i\pi$ is purely imaginary.
--
--   **Novelty.** Not asserted. It is Brownawell's Corollary 5 (1974, p. 23) at $\eta = t/\pi$, followed by rational scaling. The statement for general $a, b$ was not found in the sources read.
-- source:
--   Immediate from W. D. Brownawell, The algebraic independence of certain numbers related by the exponential function, J. Number Theory 6 (1974), 22–31, Cor. 5 (p. 23), at η = t/π, followed by rational scaling; the case a = b = 1 is DiazModulus.recip_pi_log_of_torsion_rational_modulus. The statement for general a, b was not found in the sources read. Formal proof: Diaz modulus mission, 4 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem recip_pi_log_of_rational_quadratic_relation (t : ℝ) (ht : t ≠ 0)
    (he : IsAlgebraic ℚ (Complex.exp (t : ℂ))) (a b c : ℚ) (ha : a ≠ 0)
    (hrel : (a : ℝ) * t ^ 2 + (b : ℝ) * Real.pi ^ 2 = (c : ℝ))
    (γ : ℚ) (hγ : γ ≠ 0) :
    Transcendental ℚ (Complex.exp (Complex.I * (γ : ℂ) / ((Real.pi : ℝ) : ℂ))) := by
  sorry

end DiazModulus
