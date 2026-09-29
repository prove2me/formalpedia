-- Prove2me | Theorems.Thm_DiracEquation_alphaBeta_hermitian_anticommute
-- name    : DiracEquation.alphaBeta_hermitian_anticommute
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T20:25:45.528987+00:00
-- url     : https://prove2.me/theorems/0f665aed-6fc7-4f64-a87f-beeccaa308c5
-- title:
--   The Hamiltonian-form matrices $\alpha^i=\gamma^0\gamma^i$, $\beta=\gamma^0$ are Hermitian, square to $I_4$ and anticommute
-- statement:
--   In the Dirac representation put $\beta = \gamma^0$ and $\alpha^i = \gamma^0\gamma^i$ for
--   $i = 1,2,3$. Then all four matrices are Hermitian, each squares to the identity, and any two
--   distinct ones anticommute:
--
--   $$\beta^\dagger = \beta, \qquad (\alpha^i)^\dagger = \alpha^i, \qquad
--   \beta^2 = (\alpha^i)^2 = I_4,$$
--   $$\alpha^i\alpha^j + \alpha^j\alpha^i = 0 \ \ (i \neq j), \qquad
--   \alpha^i\beta + \beta\alpha^i = 0 .$$
--
--   These are exactly the properties the source requires of the four matrices appearing in the
--   non-covariant, Schrödinger-like form of the Dirac equation
--   $$i\frac{\partial\psi}{\partial t} = \bigl(-i\,\boldsymbol\alpha\cdot\nabla + \beta m\bigr)\psi ,$$
--   and they are what makes the Dirac Hamiltonian formally self-adjoint with $H^2 = -\nabla^2 + m^2$.
--
--   **Formalization Note.** The statement is a conjunction of six clauses about the explicit matrices
--   of the Dirac representation; the spatial index $i \in \{1,2,3\}$ is carried by a three-element
--   index set, so that $\alpha$ is indexed by $\{0,1,2\}$ with $\alpha$ at index $i$ equal to
--   $\gamma^0\gamma^{i+1}$.
-- source:
--   "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation). Section "Covariant formulation", paragraph on the non-covariant form: "alpha and beta are a set of four Hermitian 4x4 matrices that all anticommute with each other and square to the identity. They are related to the gamma matrices through gamma^0 = beta and gamma^i = beta alpha_i."

import Definitions.Def_DiracEquation_fields

namespace DiracEquation

theorem alphaBeta_hermitian_anticommute :
    betaDirac.conjTranspose = betaDirac ∧
    betaDirac * betaDirac = 1 ∧
    (∀ i : Fin 3, (alphaDirac i).conjTranspose = alphaDirac i) ∧
    (∀ i : Fin 3, alphaDirac i * alphaDirac i = 1) ∧
    (∀ i j : Fin 3, i ≠ j → alphaDirac i * alphaDirac j + alphaDirac j * alphaDirac i = 0) ∧
    (∀ i : Fin 3, alphaDirac i * betaDirac + betaDirac * alphaDirac i = 0) := by sorry

end DiracEquation
