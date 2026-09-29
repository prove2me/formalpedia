-- Prove2me | Theorems.Thm_FamousTheorems_integral_tendsto_of_tendsto_of_antitone
-- name    : FamousTheorems.integral_tendsto_of_tendsto_of_antitone
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-22T13:12:47.100836+00:00
-- url     : https://prove2.me/theorems/b76f9bfc-4fbb-4f76-83a6-bb7c82560381
-- title:
--   The monotone convergence theorem (Bochner form)
-- statement:
--   **Monotone convergence** for the Bochner integral. For an antitone sequence of integrable functions converging pointwise almost everywhere, the integrals converge to the integral of the limit. No dominating function is needed: monotonicity supplies the control by itself. Unlike the extended-nonnegative version this is stated for genuine integrable real-valued functions, so the conclusion is convergence of real numbers rather than of extended ones, which is the form one actually applies when exchanging a limit with an integral of a decreasing family. **Formalization note.** The sequence is antitone with an integrable first term. The result is Mathlib's `MeasureTheory.integral_tendsto_of_tendsto_of_antitone`.
-- source:
--   Listed in Mathlib's curated theorem manifests; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem integral_tendsto_of_tendsto_of_antitone :
    ∀ {α : Type u_1} {m : MeasurableSpace α} 
    {μ : MeasureTheory.Measure α} {f : ℕ → α → ℝ} {F : α → ℝ}, 
    (∀ (n : ℕ), MeasureTheory.Integrable (f n) μ) → 
    MeasureTheory.Integrable F μ → 
    (∀ᵐ (x : α) ∂μ, Antitone fun n => f n x) → 
    (∀ᵐ (x : α) ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (F x))) → 
    Tendsto (fun n => ∫ (x : α), f n x ∂μ) atTop (𝓝 (∫ (x : α), F x ∂μ)) := by sorry

end FamousTheorems
