-- Prove2me | Theorems.Thm_FamousTheorems_bounded_convergence
-- name    : FamousTheorems.bounded_convergence
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:08.005831+00:00
-- url     : https://prove2.me/theorems/c20debbd-4836-4c02-bbb4-2e84e434be6d
-- title:
--   The bounded convergence theorem
-- statement:
--   **The bounded convergence theorem.** Let $\mu$ be a finite measure and $F_n$ a sequence of a.e.-measurable real functions with $|F_n|\le C$ a.e. for a single constant $C$. If $F_n\to f$ almost everywhere, then
--   $$\int F_n\,d\mu\longrightarrow\int f\,d\mu .$$
--
--   It is the form of dominated convergence most used in probability, where measures are finite and random variables are often bounded. It is also the classical statement in Riemann-to-Lebesgue integration courses.
--
--   **Formalization note.** Mathlib's `MeasureTheory.tendsto_integral_of_dominated_convergence` with the constant bound `fun _ => C`, which is integrable because $\mu$ is finite (`integrable_const`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.tendsto_integral_of_dominated_convergence`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem bounded_convergence {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {F : ℕ → α → ℝ} {f : α → ℝ} (C : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ) (h_bound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ C)
    (h_lim : ∀ᵐ a ∂μ, Filter.Tendsto (fun n => F n a) Filter.atTop (nhds (f a))) :
    Filter.Tendsto (fun n => ∫ a, F n a ∂μ) Filter.atTop (nhds (∫ a, f a ∂μ)) := by sorry

end FamousTheorems
