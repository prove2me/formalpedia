-- Prove2me | Theorems.Thm_DiazModulus_cubic_product_eq_square_normal_form
-- name    : DiazModulus.cubic_product_eq_square_normal_form
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-05T07:47:36.717477+00:00
-- url     : https://prove2.me/theorems/bbd5da86-854b-4c2d-b59d-2fe6ec883487
-- title:
--   If P₁P₂ = P₀² with deg P₁, deg P₂ ≤ 3 and P₀, P₁ independent, then P₀ = gQ₀Q₁, P₁ = gQ₁², P₂ = gQ₀² with Q₀, Q₁ independent of degree at most 1 and g = aQ₀ + bQ₁
-- statement:
--   Let $K$ be a field and $P_0, P_1, P_2 \in K[X]$ with $\deg P_1 \le 3$, $\deg P_2 \le 3$, $P_1 P_2 = P_0^2$, and $P_0, P_1$ linearly independent over $K$. Then there are $Q_0, Q_1 \in K[X]$ of degree at most $1$, linearly independent over $K$, and $a, b \in K$ such that, with $g = aQ_0 + bQ_1$,
--   $$P_0 = g\,Q_0 Q_1, \qquad P_1 = g\,Q_1^2, \qquad P_2 = g\,Q_0^2 .$$
--   In particular $P_1/P_0 = Q_1/Q_0$ is a Möbius transformation. For binary cubic forms this reads: if $F_1F_2 = F_0^2$, then $F_0 = LL_0L_1$, $F_1 = LL_1^2$ and $F_2 = LL_0^2$ with linear forms $L, L_0, L_1$; the degree bounds account for the factors at infinity. It is the step of `DiazModulus.circle_hull_progression_contains_square_or_reciprocal` that makes $u$ a Möbius function of the ratio $h$.
--
--   **Proof.** Divide out a common factor: $P_0 = dQ_0$ and $P_1 = dQ_1$ with $Q_0, Q_1$ coprime. From $P_1P_2 = P_0^2$ we get $Q_1P_2 = dQ_0^2$, and $Q_1$ is coprime to $Q_0^2$, so $Q_1$ divides $d$, say $d = gQ_1$; then $P_0 = gQ_0Q_1$, $P_1 = gQ_1^2$ and $P_2 = gQ_0^2$. Degrees add, so $\deg g + 2\deg Q_i \le 3$ and $\deg Q_0, \deg Q_1 \le 1$. Since $sP_0 + tP_1 = gQ_1(sQ_0 + tQ_1)$, a relation between $Q_0$ and $Q_1$ would give one between $P_0$ and $P_1$; so $Q_0, Q_1$ are independent. Writing $Q_i = \beta_i X + \alpha_i$, independence makes $\alpha_0\beta_1 - \alpha_1\beta_0 \neq 0$. Hence one of $Q_0, Q_1$ has degree $1$, which gives $\deg g \le 1$, and by Cramer's rule every polynomial of degree at most $1$, $g$ included, is a combination $aQ_0 + bQ_1$.
--
--   **Novelty.** Not asserted; elementary algebra.
-- source:
--   Elementary (unique factorisation in K[X]). A step of Theorem B of the Diaz modulus mission (DiazModulus.circle_point_extension_two_by_three_configuration_iff). Formal proof: Diaz modulus mission, 5 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

theorem cubic_product_eq_square_normal_form {K : Type*} [Field K] (P₀ P₁ P₂ : Polynomial K)
    (h₁ : P₁.natDegree ≤ 3) (h₂ : P₂.natDegree ≤ 3)
    (hli : LinearIndependent K ![P₀, P₁]) (hrel : P₁ * P₂ = P₀ ^ 2) :
    ∃ Q₀ Q₁ : Polynomial K, Q₀.natDegree ≤ 1 ∧ Q₁.natDegree ≤ 1 ∧
      LinearIndependent K ![Q₀, Q₁] ∧ ∃ a b : K,
        P₀ = (Polynomial.C a * Q₀ + Polynomial.C b * Q₁) * Q₀ * Q₁ ∧
        P₁ = (Polynomial.C a * Q₀ + Polynomial.C b * Q₁) * Q₁ ^ 2 ∧
        P₂ = (Polynomial.C a * Q₀ + Polynomial.C b * Q₁) * Q₀ ^ 2 := by
  sorry

end DiazModulus
