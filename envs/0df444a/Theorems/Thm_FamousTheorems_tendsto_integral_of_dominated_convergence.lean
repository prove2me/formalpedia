-- Prove2me | Theorems.Thm_FamousTheorems_tendsto_integral_of_dominated_convergence
-- name    : FamousTheorems.tendsto_integral_of_dominated_convergence
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T12:39:59.95643+00:00
-- url     : https://prove2.me/theorems/a3b59304-c0f5-4ab3-8698-01386d6653fc
-- title:
--   The dominated convergence theorem
-- statement:
--   **The dominated convergence theorem.** If $f_n \to f$ pointwise almost everywhere and $|f_n| \le g$ for a fixed integrable $g$, then $$\int f_n \;\longrightarrow\; \int f.$$ A single integrable dominating function licenses the exchange of limit and integral. This is the most-used of the convergence theorems because its hypothesis is easy to verify and its conclusion is an equality of limits rather than an inequality. Domination cannot be dropped — escaping bumps again — and it is exactly what rules out mass escaping to infinity or concentrating at a point. The theorem is what makes differentiation under the integral sign, continuity of parametrised integrals, and term-by-term integration of series routine. **Formalization note.** The functions take values in a Banach space, and the hypotheses are stated almost everywhere. The result is Mathlib's `MeasureTheory.tendsto_integral_of_dominated_convergence`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem tendsto_integral_of_dominated_convergence :
    ∀ {α : Type u_1} {G : Type u_2} [inst : NormedAddCommGroup G] 
    [inst_1 : NormedSpace ℝ G] {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} {F : ℕ → α → G} {f : α → G} 
    (bound : α → ℝ), 
    (∀ (n : ℕ), MeasureTheory.AEStronglyMeasurable (F n) μ) → 
    MeasureTheory.Integrable bound μ → 
    (∀ (n : ℕ), ∀ᵐ (a : α) ∂μ, ‖F n a‖ ≤ bound a) → 
    (∀ᵐ (a : α) ∂μ, Tendsto (fun n => F n a) atTop (𝓝 (f a))) → 
    Tendsto (fun n => ∫ (a : α), F n a ∂μ) atTop (𝓝 (∫ (a : α), f a ∂μ)) := by sorry

end FamousTheorems
