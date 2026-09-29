-- Prove2me | Theorems.Thm_EinsteinFieldEquations_stress_energy_divergence_free
-- name    : EinsteinFieldEquations.stress_energy_divergence_free
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-21T00:42:20.708722+00:00
-- url     : https://prove2.me/theorems/321b0061-7740-467f-9581-224a40a9863e
-- title:
--   Local conservation of energy and momentum
-- statement:
--   **Local conservation of energy–momentum.** Let $g$ be a metric whose components are four times continuously differentiable, whose matrix is invertible and symmetric at every point, let $\kappa \neq 0$, and suppose that the Einstein field equations
--
--   $$G_{ab} + \Lambda\, g_{ab} = \kappa\, T_{ab}$$
--
--   hold at every point of the chart. Then the stress–energy tensor is covariantly divergence free:
--
--   $$\nabla^{a} T_{ab} \;=\; 0 \qquad \text{for all } b \in \{0,1,2,3\}.$$
--
--   This is the source's "Conservation of energy and momentum": contracting the differential Bianchi identity twice and using metric compatibility gives $\nabla^{a}G_{ab} = 0$, whence the field equations force $\nabla^{a}T_{ab} = 0$. The smoothness hypothesis is the standing regularity convention of the subject, made explicit here because the covariant divergence of the Einstein tensor involves third derivatives of the metric.
-- source:
--   Wikipedia, "Einstein field equations", https://en.wikipedia.org/wiki/Einstein_field_equations, section "Features — Conservation of energy and momentum" (derivation of local energy-momentum conservation from the contracted Bianchi identity)

import Definitions.Def_efe_geometry

namespace EinsteinFieldEquations

theorem stress_energy_divergence_free (g T : Tensor2Field) (Lam kappa : ℝ) (x : Coord)
    (hsmooth : ∀ i j : Fin 4, ContDiff ℝ 4 (fun y : Coord => g y i j))
    (hinv : ∀ y : Coord, IsUnit (g y).det)
    (hsymm : ∀ y : Coord, (g y).IsSymm)
    (hkappa : kappa ≠ 0)
    (hefe : ∀ y : Coord, SatisfiesEFE g Lam kappa T y) :
    ∀ b : Fin 4, covDiv g T b x = 0 := by sorry

end EinsteinFieldEquations
