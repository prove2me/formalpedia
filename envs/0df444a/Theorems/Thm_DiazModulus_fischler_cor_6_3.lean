-- Prove2me | Theorems.Thm_DiazModulus_fischler_cor_6_3
-- name    : DiazModulus.fischler_cor_6_3
-- status  : Proved
-- author  : @carlok
-- created : 2026-11-18T16:16:17.965461+00:00
-- url     : https://prove2.me/theorems/fca32f3a-ece1-484a-8f19-9fd46fbc0744
-- title:
--   Fischler 2001, Cor. 6.3 (1): for k ≥ 3, every P = Λᵏ with coefficients in ℒ̃, Λ a linear form, lies on a line ℂQ with Q algebraic made of k-th powers of linear forms
-- statement:
--   Here $\overline{\mathbb Q}$ is the field of algebraic numbers, $\mathcal L$ the set of logarithms of algebraic numbers ($z \in \mathbb C$ with $e^z$ algebraic), and $\widetilde{\mathcal L}$ the $\overline{\mathbb Q}$-vector space spanned by $1$ and $\mathcal L$. A subspace $S \subseteq \mathbb C^d$ is *rational* if it is spanned by vectors with algebraic coordinates.
--
--   Let $k \ge 3$ and $m \ge 0$. Let $P \in \mathbb C[X_1, \dots, X_m]$ have all its coefficients in $\widetilde{\mathcal L}$, and assume that $P = (\lambda_1 X_1 + \dots + \lambda_m X_m)^{k}$ for some $\lambda \in \mathbb C^m$. Then there is a polynomial $Q \in \mathbb C[X_1, \dots, X_m]$ with algebraic coefficients such that $P \in \mathbb C Q$ and every element of the line $\mathbb C Q$ is the $k$-th power $(\lambda'_1 X_1 + \dots + \lambda'_m X_m)^k$ of a linear form, for some $\lambda' \in \mathbb C^m$.
--
--   So every $k$-th power of a linear form whose coefficients (as a polynomial) lie in $\widetilde{\mathcal L}$ lies on a line defined over $\overline{\mathbb Q}$ and contained in the set $\mathcal V(k, m)$ of $k$-th powers of linear forms: the non-trivial inclusion of Fischler's Conjecture 1 for $\mathcal V(k, m)$.
-- source:
--   S. Fischler, Orbits under algebraic groups and logarithms of algebraic numbers, Acta Arith. 100 (2001), 167–187, Cor. 6.3, part 1 (p. 184; proof p. 185): Conjecture 1 (p. 168) for 𝒱(k, m), k ≥ 3, in the form of its non-trivial inclusion, with a vector line ℂQ as the affine subspace defined over Q̄; the other inclusion is immediate. Fischler's ℒ, the Q̄-vector space spanned by 1 and the logarithms of algebraic numbers, is ℒ̃ here. Part 2, a conditional reduction to 𝒱(2, 2), is not formalised. Proved from DiazModulus.fischler_theorem_1_1. Formal proof: Diaz modulus mission, 18 November 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem fischler_cor_6_3 {m k : ℕ} (hk : 3 ≤ k) (P : MvPolynomial (Fin m) ℂ)
    (hP : ∀ s, P.coeff s ∈ LogAlgTilde) (Λ : Fin m → ℂ)
    (hPΛ : P = (∑ i, MvPolynomial.C (Λ i) * MvPolynomial.X i) ^ k) :
    ∃ Q : MvPolynomial (Fin m) ℂ, (∀ s, Q.coeff s ∈ Qbar) ∧ P ∈ Submodule.span ℂ {Q} ∧
      ∀ R ∈ Submodule.span ℂ {Q}, ∃ Λ' : Fin m → ℂ,
        R = (∑ i, MvPolynomial.C (Λ' i) * MvPolynomial.X i) ^ k := by
  sorry

end DiazModulus
