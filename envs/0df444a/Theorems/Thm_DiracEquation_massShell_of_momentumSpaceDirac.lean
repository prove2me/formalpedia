-- Prove2me | Theorems.Thm_DiracEquation_massShell_of_momentumSpaceDirac
-- name    : DiracEquation.massShell_of_momentumSpaceDirac
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T20:25:20.161333+00:00
-- url     : https://prove2.me/theorems/d6e02c99-d163-4887-a5ca-625cd2d3add5
-- title:
--   A nonzero solution of $(p\!\!\!/+m)u=0$ lies on the mass shell $p_\mu p^\mu = m^2$
-- statement:
--   Let $\gamma$ satisfy the Clifford relation $\gamma^\mu\gamma^\nu + \gamma^\nu\gamma^\mu =
--   2\eta^{\mu\nu}I_4$ with $\eta = \operatorname{diag}(1,-1,-1,-1)$, let $m \in \mathbb{R}$, let
--   $p = (p_\mu)$ be a real covector, and let $u \in \mathbb{C}^4$ be **nonzero** with
--
--   $$\bigl(p\!\!\!/ + m\bigr)u = 0 .$$
--
--   Then $p$ lies on the mass shell:
--
--   $$\eta^{\mu\nu} p_\mu p_\nu \;=\; p_0^2 - p_1^2 - p_2^2 - p_3^2 \;=\; m^2 .$$
--
--   Combined with the plane-wave construction this is the dispersion relation of the free Dirac
--   field: a plane wave built from a nonzero polarization has energy $p_0 = \pm\sqrt{|\mathbf p|^2 +
--   m^2}$, which is the origin of the positive- and negative-frequency solutions and, historically, of
--   the prediction of antimatter.
--
--   **Formalization Note.** The hypothesis $u \neq 0$ is essential rather than cosmetic: for $u = 0$
--   the momentum-space equation holds for every $p$, and the conclusion would be false. The equality
--   is stated between complex numbers, the real quantities being coerced.
-- source:
--   "Dirac equation", Wikipedia, https://en.wikipedia.org/wiki/Dirac_equation, sections "Formulation - Covariant formulation" (Dirac equation, Clifford relation {gamma^mu, gamma^nu} = 2 eta^{mu nu} I_4, Dirac representation of the gamma matrices, Hamiltonian form with alpha and beta) and "Properties - Plane wave solutions" (Klein-Gordon reduction, plane waves, momentum-space Dirac equation). Section "Plane wave solutions": the momentum-space Dirac equation (p-slash + m) u(p) = 0 together with the positive energy p_0 = sqrt(|p|^2 + m^2).

import Definitions.Def_DiracEquation_fields

namespace DiracEquation

theorem massShell_of_momentumSpaceDirac (g : Fin 4 → Matrix (Fin 4) (Fin 4) ℂ)
    (hg : IsGammaFamily g) (m : ℝ) (p : Fin 4 → ℝ) (u : Fin 4 → ℂ) (hu0 : u ≠ 0)
    (hu : (slash g fun mu => (p mu : ℂ)).mulVec u + (m : ℂ) • u = 0) :
    ∑ mu, eta mu mu * (p mu : ℂ) ^ 2 = (m : ℂ) ^ 2 := by sorry

end DiracEquation
