-- Prove2me | Theorems.Thm_FamousTheorems_ae_differentiablewithinat
-- name    : FamousTheorems.ae_differentiablewithinat
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:01:08.351742+00:00
-- url     : https://prove2.me/theorems/1e1f750d-e457-4ee7-8310-a048103f56ab
-- title:
--   Rademacher's theorem
-- statement:
--   **Rademacher's theorem.** A Lipschitz function between finite-dimensional real spaces is differentiable almost everywhere. A one-sided modulus of continuity — no more than a uniform bound on difference quotients — forces genuine differentiability off a null set. This is sharp in the sense that the exceptional set can be dense and uncountable, as the absolute value function's single bad point already hints and more elaborate examples confirm. The theorem is what makes Lipschitz maps usable in geometric measure theory, underlies the area and coarea formulas, and is the reason Sobolev functions in $W^{1,\infty}$ can be treated pointwise. **Formalization note.** `LipschitzOnWith K f s` is the Lipschitz condition on a set, and differentiability is asserted almost everywhere within it. The result is Mathlib's `LipschitzOnWith.ae_differentiableWithinAt`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem ae_differentiablewithinat :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
    [inst_2 : MeasurableSpace E] [BorelSpace E] {F : Type u_2} [inst_4 : NormedAddCommGroup F] [inst_5 : NormedSpace ℝ F] 
    {C : NNReal} {s : Set E} {μ : MeasureTheory.Measure E} [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] 
    [μ.IsAddHaarMeasure] {f : E → F}, 
    LipschitzOnWith C f s → MeasurableSet s → ∀ᵐ (x : E) ∂μ.restrict s, DifferentiableWithinAt ℝ f s x := by sorry

end FamousTheorems
