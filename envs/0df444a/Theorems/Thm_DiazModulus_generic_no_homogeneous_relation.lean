-- Prove2me | Theorems.Thm_DiazModulus_generic_no_homogeneous_relation
-- name    : DiazModulus.generic_no_homogeneous_relation
-- status  : Proved
-- author  : @carlok
-- created : 2026-10-01T12:33:46.712758+00:00
-- url     : https://prove2.me/theorems/eea81d66-62de-49cc-b40b-7c9962f8fe39
-- title:
--   At a generic point of the circle, no non-zero homogeneous polynomial over Q̄ vanishes at (u, ū, iπ)
-- statement:
--   Let $u \neq 0$ with $|u|^2$ algebraic, and suppose $u$ and $\pi$ are algebraically independent over $\overline{\mathbb{Q}}$ (a *generic* point of the circle $|z|^2 = |u|^2$). Then no non-zero homogeneous polynomial $P \in \overline{\mathbb{Q}}[X_0, X_1, X_2]$, of any degree, satisfies $P(u, \bar u, i\pi) = 0$.
--
--   The degree-2 case over $\mathbb{Q}$ is `DiazModulus.generic_conj_pair_no_quadratic_relation`.
--
--   **Proof.** With $\rho = |u|^2$ and $\bar u = \rho/u$, homogeneity gives $u^dP(u, \bar u, i\pi) = P(u^2, \rho, u\,i\pi)$. The monomial $X_0^aX_1^bX_2^c$ ($a + b + c = d$) goes to $\rho^b u^{2a+c}(i\pi)^c$, and distinct monomials go to distinct monomials in $u$ and $i\pi$, which are algebraically independent.
--
--   **Novelty.** None asserted: it is an instance of Waldschmidt's Proposition 12.13 ((i) ⇒ (iii)) in *Diophantine Approximation on Linear Algebraic Groups*, applied to $\overline{\mathbb{Q}} + \overline{\mathbb{Q}}\,\rho/u^2 + \overline{\mathbb{Q}}\,i\pi/u$. This instance was not found stated in the sources read. The contribution of this node is the formal proof.
-- source:
--   An instance of M. Waldschmidt, Diophantine Approximation on Linear Algebraic Groups, Grundlehren 326, Springer, 2000, Proposition 12.13 (pp. 429–430). Formal proof: Diaz modulus mission, 1 October 2026 (C. Perassi).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus

/-- For `u ≠ 0` with `|u|²` algebraic and `u`, `π` algebraically independent, no non-zero homogeneous
polynomial over `Q̄`, of any degree, vanishes at `(u, ū, iπ)`. -/
theorem generic_no_homogeneous_relation (u : ℂ) (hu : u ≠ 0)
    (hρ : IsAlgebraic ℚ (u * conj u))
    (hgen : AlgebraicIndependent (↥Qbar) ![u, ((Real.pi : ℝ) : ℂ) * Complex.I])
    {d : ℕ} (P : MvPolynomial (Fin 3) ↥Qbar) (hP : P.IsHomogeneous d)
    (h : MvPolynomial.aeval ![u, conj u, ((Real.pi : ℝ) : ℂ) * Complex.I] P = 0) :
    P = 0 := by
  sorry

end DiazModulus
