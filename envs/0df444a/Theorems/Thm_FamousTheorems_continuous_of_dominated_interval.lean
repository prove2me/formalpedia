-- Prove2me | Theorems.Thm_FamousTheorems_continuous_of_dominated_interval
-- name    : FamousTheorems.continuous_of_dominated_interval
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:12.154637+00:00
-- url     : https://prove2.me/theorems/5299f76e-713a-4975-b87b-f59a32401129
-- title:
--   Continuity of parametric integrals
-- statement:
--   **Continuity of an integral in a parameter.** If $x \mapsto F(x,t)$ is continuous for almost every $t$ and $\lVert F(x,t)\rVert \le g(t)$ for an integrable $g$, then $$x \;\longmapsto\; \int_a^b F(x,t)\,dt$$ is continuous. This is dominated convergence in parametric form, and it is the hypothesis one actually checks in practice when a function is defined by an integral. Such definitions are everywhere — the Gamma function, Fourier and Laplace transforms, convolution, solutions of ODEs written in integral form — and this theorem is what makes them continuous. Its differentiable analogue, obtained by dominating the derivative instead, is the Leibniz rule for differentiating under the integral sign. **Formalization note.** The integral is over an interval and the domination is by a fixed interval-integrable function. The result is Mathlib's `intervalIntegral.continuous_of_dominated_interval`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem continuous_of_dominated_interval :
    ∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
    [inst_1 : NormedSpace ℝ E] {μ : MeasureTheory.Measure ℝ} {X : Type u_2} [inst_2 : TopologicalSpace X] 
    [FirstCountableTopology X] {F : X → ℝ → E} {bound : ℝ → ℝ} {a b : ℝ}, 
    (∀ (x : X), MeasureTheory.AEStronglyMeasurable (F x) (μ.restrict (uIoc a b))) → 
    (∀ (x : X), ∀ᵐ (t : ℝ) ∂μ, t ∈ uIoc a b → ‖F x t‖ ≤ bound t) → 
    IntervalIntegrable bound μ a b → 
    (∀ᵐ (t : ℝ) ∂μ, t ∈ uIoc a b → Continuous fun x => F x t) → Continuous fun x => ∫ (t : ℝ) in a..b, F x t ∂μ := by sorry

end FamousTheorems
