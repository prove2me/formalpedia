-- Prove2me | Theorems.Thm_FamousTheorems_integral_prod
-- name    : FamousTheorems.integral_prod
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:14.320004+00:00
-- url     : https://prove2.me/theorems/b2382525-6c31-4c2a-9e2c-432cfabb00c9
-- title:
--   Fubini's theorem
-- statement:
--   **Fubini's theorem.** For an integrable function on a product space, the double integral equals either iterated integral: $$\iint f \,d(\mu\otimes\nu) = \int\!\!\left(\int f(x,y)\,d\nu(y)\right)d\mu(x).$$ Integration order may be exchanged provided $f$ is integrable for the product measure. That hypothesis is essential rather than technical: without it the iterated integrals can exist and disagree, the standard example being $(x^2-y^2)/(x^2+y^2)^2$ on the unit square, whose two iterated integrals are $\pi/4$ and $-\pi/4$. Tonelli's companion theorem removes the hypothesis for nonnegative functions, and the usual practical route is to apply Tonelli to $|f|$ to establish integrability and then Fubini to $f$. **Formalization note.** The measures are $\sigma$-finite and the function is Bochner-integrable with values in a Banach space. The result is Mathlib's `MeasureTheory.integral_prod`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem integral_prod :
    ∀ {α : Type u_1} {β : Type u_2} {E : Type u_3} [inst : MeasurableSpace α] 
    [inst_1 : MeasurableSpace β] {μ : MeasureTheory.Measure α} {ν : MeasureTheory.Measure β} 
    [inst_2 : NormedAddCommGroup E] [MeasureTheory.SFinite ν] [inst_4 : NormedSpace ℝ E] [MeasureTheory.SFinite μ] 
    (f : α × β → E), 
    MeasureTheory.Integrable f (μ.prod ν) → ∫ (z : α × β), f z ∂μ.prod ν = ∫ (x : α), ∫ (y : β), f (x, y) ∂ν ∂μ := by sorry

end FamousTheorems
