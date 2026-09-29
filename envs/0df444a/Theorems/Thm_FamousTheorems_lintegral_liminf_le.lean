-- Prove2me | Theorems.Thm_FamousTheorems_lintegral_liminf_le
-- name    : FamousTheorems.lintegral_liminf_le
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:39:59.381486+00:00
-- url     : https://prove2.me/theorems/ee16f133-38f6-4501-95c2-656f79546ff4
-- title:
--   Fatou's lemma
-- statement:
--   **Fatou's lemma.** For nonnegative measurable functions, $$\int \liminf_n f_n \;\le\; \liminf_n \int f_n.$$ Mass can be lost in the limit but never gained. The inequality is genuinely one-directional: a bump of fixed height escaping to infinity has liminf zero pointwise while every integral stays equal to one, so equality fails. What the lemma provides is a free lower-semicontinuity statement requiring no domination and no monotonicity, only nonnegativity. It is the workhorse behind existence proofs in the calculus of variations, where one extracts a limit of a minimising sequence and needs the limit's energy to be no larger. **Formalization note.** The functions are `ℝ≥0∞`-valued, so nonnegativity is automatic and no integrability hypothesis is required. The result is Mathlib's `MeasureTheory.lintegral_liminf_le`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem lintegral_liminf_le :
    ∀ {α : Type u_1} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} 
    {ι : Type u_2} {f : ι → α → ENNReal} {u : Filter ι} [u.IsCountablyGenerated], 
    (∀ (i : ι), Measurable (f i)) → ∫⁻ (a : α), liminf (fun i => f i a) u ∂μ ≤ liminf (fun i => ∫⁻ (a : α), f i a ∂μ) u := by sorry

end FamousTheorems
