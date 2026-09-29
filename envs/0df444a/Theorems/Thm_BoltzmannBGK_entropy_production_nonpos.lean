-- Prove2me | Theorems.Thm_BoltzmannBGK_entropy_production_nonpos
-- name    : BoltzmannBGK.entropy_production_nonpos
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-19T22:21:05.127767+00:00
-- url     : https://prove2.me/theorems/d1a62fe0-286e-416e-a11f-8b400cebff18
-- title:
--   Entropy production of the BGK operator: $\int (\log f)\,C[f]\,\mathrm dv\le 0$
-- statement:
--   Let $\tau>0$ and let $f$ be an admissible distribution function on velocity space: everywhere strictly positive, integrable, with finite second velocity moment; assume in addition that the entropy-production integrand $v\mapsto(\log f(v))\,C[f](v)$ is integrable. Then
--
--   $$\int_{\mathbb R^3}\mathrm dv\,(\log f)\,C[f]\;\le\;0 .$$
--
--   This is the inequality of part (b) of the source question, and it is the $H$-theorem for the BGK model: writing $H=\int f\log f\,\mathrm dv$, the collision term contributes $\mathrm dH/\mathrm dt=\int (\log f)C[f]\,\mathrm dv\le 0$, so collisions never decrease the entropy $-H$.
--
--   The characterisation of the equality case is stated separately as the goal of this mission.
--
--   **Formalization Note** The integrability hypothesis is essential: in Lean the integral of a non-integrable function is $0$, so without it the inequality would hold for uninteresting reasons.
-- source:
--   Oxford Honour School of Mathematical and Theoretical Physics Part C / MSc in Mathematical and Theoretical Physics, examination paper A15089W1, KINETIC THEORY, Hilary Term 2019 (Thursday 10 January 2019), Question 1, page 2. https://web.archive.org/web/20250913150648/https://mmathphys.physics.ox.ac.uk/sites/default/files/mmathphys/documents/media/kt_2019.pdf Part (b), the inequality int dv (log f) C[f] <= 0.

import Definitions.Def_BoltzmannBGK_model

open MeasureTheory Real

namespace BoltzmannBGK

theorem entropy_production_nonpos (τ : ℝ) (f : Vel → ℝ) (hτ : 0 < τ)
    (hf : IsKineticState f)
    (hint : Integrable fun v => Real.log (f v) * collision τ f v) :
    ∫ v, Real.log (f v) * collision τ f v ≤ 0 := by sorry

end BoltzmannBGK
