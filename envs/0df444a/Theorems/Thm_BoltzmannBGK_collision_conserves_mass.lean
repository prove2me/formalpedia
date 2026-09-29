-- Prove2me | Theorems.Thm_BoltzmannBGK_collision_conserves_mass
-- name    : BoltzmannBGK.collision_conserves_mass
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:19:43.030677+00:00
-- url     : https://prove2.me/theorems/75a72c69-cf24-4970-8485-c0270406f819
-- title:
--   BGK conserves mass: $\int C[f]\,\mathrm dv=0$
-- statement:
--   Let $\tau>0$ and let $f$ be an admissible distribution function on velocity space: everywhere strictly positive, integrable, and with finite second velocity moment. Then the BGK collision operator $C[f]=-\tfrac1\tau(f-f^{(0)})$ conserves mass,
--
--   $$\int_{\mathbb R^3} C[f](v)\,\mathrm dv=0 .$$
--
--   Equivalently, $f$ and its local Maxwellian $f^{(0)}$ carry the same mass density $\rho$, by construction of $f^{(0)}$. This is the first of the three collision invariants of part (a) of the source question; together with the momentum and energy identities it is what makes the BGK model compatible with the macroscopic conservation laws.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a), conservation of rho by the BGK collision operator.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem collision_conserves_mass (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f) :
    ∫ v, collision τ f v = 0 := by sorry

end BoltzmannBGK
