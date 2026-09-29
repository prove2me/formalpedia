-- Prove2me | Theorems.Thm_BoltzmannBGK_collision_conserves_momentum
-- name    : BoltzmannBGK.collision_conserves_momentum
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:20:11.233565+00:00
-- url     : https://prove2.me/theorems/65a5d95f-9a7e-41a3-b015-37e38ba99c30
-- title:
--   BGK conserves momentum: $\int v\,C[f]\,\mathrm dv=0$
-- statement:
--   Let $\tau>0$ and let $f$ be an admissible distribution function: everywhere strictly positive, integrable, with finite second velocity moment. The BGK collision operator conserves momentum,
--
--   $$\int_{\mathbb R^3} v\,C[f](v)\,\mathrm dv=0\in\mathbb R^3 .$$
--
--   Equivalently, $f$ and its local Maxwellian $f^{(0)}$ carry the same momentum density $\rho u$. This is the second collision invariant of part (a); it is what makes the momentum equation of the BGK model free of a collisional source term.
--
--   **Formalization Note** Both sides are vectors; the integral is a vector-valued (Bochner) integral.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (a), conservation of u by the BGK collision operator.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem collision_conserves_momentum (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f) :
    ∫ v, collision τ f v • v = 0 := by sorry

end BoltzmannBGK
