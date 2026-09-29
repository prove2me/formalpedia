-- Prove2me | Theorems.Thm_DiracEquation_dirac_implies_kleinGordon
-- name    : DiracEquation.dirac_implies_kleinGordon
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T19:41:15.894993+00:00
-- url     : https://prove2.me/theorems/d42777e8-7075-408b-94f5-335456145db3
-- title:
--   Every $C^2$ solution of the Dirac equation solves the Klein--Gordon equation
-- statement:
--   Let $\gamma = (\gamma^0,\gamma^1,\gamma^2,\gamma^3)$ be complex $4\times4$ matrices satisfying the
--   Clifford relation
--   $$\gamma^\mu\gamma^\nu + \gamma^\nu\gamma^\mu = 2\eta^{\mu\nu} I_4, \qquad
--   \eta = \operatorname{diag}(1,-1,-1,-1),$$
--   let $m \in \mathbb{R}$, and let $\psi : \mathbb{R}^4 \to \mathbb{C}^4$ be twice continuously
--   differentiable. If $\psi$ satisfies the Dirac equation
--   $$\bigl(i\gamma^\mu\partial_\mu - m\bigr)\psi(x) = 0 \quad \text{for all } x,$$
--   then each component of $\psi$ satisfies the Klein--Gordon equation
--
--   $$\bigl(\partial_\mu\partial^\mu + m^2\bigr)\psi(x) = 0 \quad \text{for all } x, \qquad
--   \partial_\mu\partial^\mu = \partial_0^2 - \partial_1^2 - \partial_2^2 - \partial_3^2 .$$
--
--   This is the statement that the Dirac operator is a square root of the wave operator: applying
--   $(i\gamma^\nu\partial_\nu + m)$ to the Dirac equation produces the Klein--Gordon operator. It is
--   the reason the free Dirac field has the relativistic dispersion relation $p_\mu p^\mu = m^2$ and
--   can be expanded in plane waves, and it holds for every family of gamma matrices, not only for a
--   particular representation.
--
--   **Formalization Note.** Partial derivatives are Fréchet derivatives along the coordinate
--   directions of $\mathbb{R}^4$, the hypothesis is $C^2$ regularity of $\psi$ on all of
--   $\mathbb{R}^4$, and both equations are imposed pointwise at every $x$.
-- source:
--   "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation). Section "Plane wave solutions", first displayed equation: (i d-slash + m)(i d-slash - m) psi = (d_mu d^mu + m^2) psi = 0.

import Definitions.Def_DiracEquation_fields

namespace DiracEquation

theorem dirac_implies_kleinGordon (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ) (hg : IsGammaFamily g)
    (m : ℝ) (psi : (Fin 4 → ℝ) → (Fin 4 → ℂ)) (hpsi : ContDiff ℝ 2 psi)
    (hD : IsDiracSolution g m psi) : IsKleinGordonSolution m psi := by sorry

end DiracEquation
