-- Prove2me | Theorems.Thm_FamousTheorems_tendstouniformlyon_of_ae_tendsto
-- name    : FamousTheorems.tendstouniformlyon_of_ae_tendsto
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:13:04.42273+00:00
-- url     : https://prove2.me/theorems/46d28648-aba6-4dda-b03d-a188af919a5e
-- title:
--   Egorov's theorem
-- statement:
--   **Egorov's theorem.** On a finite measure space, almost-everywhere convergence implies uniform convergence off a set of arbitrarily small measure. Pointwise convergence is nearly uniform: the failure is confined to a set that can be made as small as one likes, though not empty, as $x^n$ on $[0,1]$ shows. Finiteness of the measure is essential and the statement fails on the real line with Lebesgue measure. It is one of Littlewood's three principles and the standard bridge for transferring results needing uniformity to the almost-everywhere setting. **Formalization note.** The conclusion is `TendstoUniformlyOn` off a set of measure below any given epsilon. The result is Mathlib's `MeasureTheory.tendstoUniformlyOn_of_ae_tendsto`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem tendstouniformlyon_of_ae_tendsto :
    ∀ {α : Type u_1} {β : Type u_2} {ι : Type u_3} {m : MeasurableSpace α} 
    [inst : PseudoEMetricSpace β] {μ : MeasureTheory.Measure α} [inst_1 : SemilatticeSup ι] [Nonempty ι] [Countable ι] 
    {f : ι → α → β} {g : α → β} {s : Set α}, 
    (∀ (n : ι), MeasureTheory.StronglyMeasurable (f n)) → 
    MeasureTheory.StronglyMeasurable g → 
    MeasurableSet s → 
    μ s ≠ ⊤ → 
    (∀ᵐ (x : α) ∂μ, x ∈ s → Tendsto (fun n => f n x) atTop (𝓝 (g x))) → 
    ∀ {ε : ℝ}, 0 < ε → ∃ t ⊆ s, MeasurableSet t ∧ μ t ≤ ENNReal.ofReal ε ∧ TendstoUniformlyOn f g atTop (s \ t) := by sorry

end FamousTheorems
