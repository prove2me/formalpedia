-- Prove2me | Theorems.Thm_DiazModulus_fischler_theorem_1_1
-- name    : DiazModulus.fischler_theorem_1_1
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:26.826146+00:00
-- url     : https://prove2.me/theorems/20d75a7a-cdb0-48ae-bf68-762001ec7fc3
-- title:
--   Fischler 2001, Th. 1.1: if k ≥ 3 and P = (λ₁X₁ + ⋯ + λₘXₘ)ᵏ has all its coefficients in ℒ̃, then P = aφᵏ with a ∈ ℒ̃ and φ a linear form with algebraic coefficients
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $k \ge 3$ and $m \ge 0$. Let $P \in \mathbb C[X_1, \dots, X_m]$ have all its coefficients in $\widetilde{\mathcal L}$, and assume that $P = (\lambda_1 X_1 + \dots + \lambda_m X_m)^{k}$ for some $\lambda \in \mathbb C^m$. Then there are $\varphi_1, \dots, \varphi_m \in \overline{\mathbb Q}$ and $a \in \widetilde{\mathcal L}$ such that
--   $$P = a\,(\varphi_1 X_1 + \dots + \varphi_m X_m)^k.$$
--   The printed hypothesis that $P$ is homogeneous of degree $k$ is not stated: it follows from $P$ being the power of a linear form.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Th. 1.1 (pp. 168–169), complex case; it is Th. 6.2 (1) (p. 184), here for any m. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. The printed hypothesis that P is homogeneous of degree k is implied by P = Λᵏ and is omitted. The printed proof (of Th. 6.2, pp. 184–185) stops at n ≤ 1 and leaves implicit why a lies in ℒ̃; here a = c₀ᵏ is a Q̄-multiple of the coefficient λⱼᵏ of Xⱼᵏ in P. Proved from DiazModulus.fischler_linear_pow_prod_mem, DiazModulus.fischler_power_span_finrank and DiazModulus.fischler_rational_hull. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_theorem_1_1 {m k : ℕ} (hk : 3 ≤ k) (P : MvPolynomial (Fin m) ℂ)
    (hP : ∀ s, P.coeff s ∈ LogAlgTilde) (Λ : Fin m → ℂ)
    (hPΛ : P = (∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ k) :
    ∃ φ : Fin m → ℂ, (∀ i, φ i ∈ Qbar) ∧ ∃ a ∈ LogAlgTilde,
      P = MvPolynomial.C a * (∑ i, MvPolynomial.C (φ i) * MvPolynomial.X i) ^ k := by
  sorry

end DiazModulus
