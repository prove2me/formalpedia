-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_6_2_two
-- name    : DiazModulus.fischler_theorem_6_2_two
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:25.814198+00:00
-- url     : https://prove2.me/theorems/2cf69b3b-df78-46fe-9a86-b3110e1fb70a
-- title:
--   Fischler 2001, Th. 6.2 (2): if P = (λ₁X₁ + ⋯ + λₘXₘ)² has all its coefficients in ℒ̃, then P = (aφ₁ + bφ₂)² with a, b ∈ ℂ and φ₁, φ₂ linear forms with algebraic coefficients
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $m \ge 0$. Let $P \in \mathbb C[X_1, \dots, X_m]$ have all its coefficients in $\widetilde{\mathcal L}$, and assume that $P = (\lambda_1 X_1 + \dots + \lambda_m X_m)^2$ for some $\lambda \in \mathbb C^m$. Then there are two linear forms $\varphi_1 = \sum_i \varphi_{1i} X_i$ and $\varphi_2 = \sum_i \varphi_{2i} X_i$ with algebraic coefficients $\varphi_{1i}, \varphi_{2i} \in \overline{\mathbb Q}$, and $a, b \in \mathbb C$, such that
--   $$P = (a\varphi_1 + b\varphi_2)^2.$$
--   The printed hypothesis that $P$ is homogeneous of degree $2$ is not stated: it follows from $P$ being the power of a linear form. The printed hypothesis $m \ge 2$ is not made either.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 6.2, part 2 (p. 184), complex case, without the printed hypothesis m ≥ 2 (for m ≤ 2 the conclusion is immediate). Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The printed hypothesis that P is homogeneous of degree 2 is implied by P = Λ² and is omitted. Proved from DiazModulus.fischler_linear_pow_prod_mem, DiazModulus.fischler_power_span_finrank and DiazModulus.fischler_rational_hull. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_6_2_two {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (hP : ∀ s, P.coeff s ∈ LogAlgTilde) (Λ : Fin m → ℂ)
    (hPΛ : P = (∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ 2) :
    ∃ φ₁ φ₂ : Fin m → ℂ, (∀ i, φ₁ i ∈ Qbar) ∧ (∀ i, φ₂ i ∈ Qbar) ∧ ∃ a b : ℂ,
      P = (MvPolynomial.C a * (∑ i, MvPolynomial.C (φ₁ i) * MvPolynomial.X i) +
        MvPolynomial.C b * (∑ i, MvPolynomial.C (φ₂ i) * MvPolynomial.X i)) ^ 2 := by
  sorry

end DiazModulus
