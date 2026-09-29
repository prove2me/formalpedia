-- Prove2me | Theorems.Thm_FamousTheorems_tendsto_approxon
-- name    : FamousTheorems.tendsto_approxon
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:40:01.579455+00:00
-- url     : https://prove2.me/theorems/2d8a5b95-f383-4b3e-945c-84e3b563781d
-- title:
--   Approximation by simple functions
-- statement:
--   **Approximation by simple functions.** Every measurable function is the pointwise limit of an increasing sequence of simple (finitely-valued measurable) functions. This is the construction that makes the Lebesgue integral definable: one defines the integral for simple functions, where it is a finite sum, and extends by monotone limits. The approximating sequence is explicit — dyadic truncation of the range rather than the domain — which is exactly the difference between the Lebesgue and Riemann approaches and the reason Lebesgue's integral handles wildly discontinuous functions. The result is also the standard device for proving statements about all measurable functions: verify for simple functions, then pass to the limit. **Formalization note.** `SimpleFunc.approxOn` is the explicit approximating sequence, converging pointwise within a given closed set of values. The result is Mathlib's `MeasureTheory.SimpleFunc.tendsto_approxOn`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem tendsto_approxon :
    ∀ {α : Type u_1} {β : Type u_2} [inst : MeasurableSpace α] 
    [inst_1 : PseudoEMetricSpace α] [inst_2 : OpensMeasurableSpace α] [inst_3 : MeasurableSpace β] {f : β → α} 
    (hf : Measurable f) {s : Set α} {y₀ : α} (h₀ : y₀ ∈ s) [inst_4 : TopologicalSpace.SeparableSpace ↑s] {x : β}, 
    f x ∈ closure s → Tendsto (fun n => (MeasureTheory.SimpleFunc.approxOn f hf s y₀ h₀ n) x) atTop (𝓝 (f x)) := by sorry

end FamousTheorems
