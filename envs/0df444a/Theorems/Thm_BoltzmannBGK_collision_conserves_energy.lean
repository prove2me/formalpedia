-- Prove2me | Theorems.Thm_BoltzmannBGK_collision_conserves_energy
-- name    : BoltzmannBGK.collision_conserves_energy
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:20:32.515294+00:00
-- url     : https://prove2.me/theorems/7c8928d2-8a11-4a9c-89f3-ade293a5289e
-- title:
--   BGK conserves energy: $\int |v|^2 C[f]\,\mathrm dv=0$
-- statement:
--   Let $\tau>0$ and let $f$ be an admissible distribution function: everywhere strictly positive, integrable, with finite second velocity moment. The BGK collision operator conserves energy,
--
--   $$\int_{\mathbb R^3}|v|^2\,C[f](v)\,\mathrm dv=0 .$$
--
--   Since the particles have unit mass, $\tfrac12|v|^2$ is the kinetic energy of a particle, so this says that collisions redistribute energy among the particles without changing the total energy density $\tfrac12\rho\big(|u|^2+3\theta\big)$. It is the third collision invariant of part (a), and together with the mass and momentum identities it expresses the conservation of $\rho$, $u$ and $\theta$ by the collision operator.
--
--   **Formalization Note** The moment is taken about the origin; combined with the mass and momentum identities it is equivalent to the vanishing of the central second moment of $C[f]$.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a), conservation of theta (energy) by the BGK collision operator.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem collision_conserves_energy (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f) :
    ∫ v, ‖v‖ ^ 2 * collision τ f v = 0 := by sorry

end BoltzmannBGK
