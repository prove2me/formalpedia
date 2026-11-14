-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB218_bounded_joint_mesh_L2_limit_implies_nested_pair_cauchy
-- name    : AvramDividend.Classical.avram_gbB218_bounded_joint_mesh_L2_limit_implies_nested_pair_cauchy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:28:28.090369+00:00
-- url     : https://prove2.me/theorems/936f4044-1e2c-4217-b37b-6911c4cbd144
-- title:
--   Jointly measurable uniformly bounded coefficients with common nested L2 limit are pairwise nested-L2 Cauchy
-- statement:
--   For any pair of finite measures and a jointly measurable uniformly bounded family of coefficients and common limit, convergence of the iterated expected squared errors to zero forces simultaneous convergence to zero of the iterated expected squared differences between two meshes.
-- source:
--   Generic reusable original Gaussian B216 -> pairwise energy certificate; B138 integrability + B217 quantitative squared triangle conversion.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB218_bounded_joint_mesh_L2_limit_implies_nested_pair_cauchy
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ℕ → α → β → ℝ) (g : α → β → ℝ)
    (hf : ∀ m, Measurable (fun z : α × β => f m z.1 z.2))
    (hg : Measurable (fun z : α × β => g z.1 z.2))
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m a b, |f m a b| ≤ B)
    (hgb : ∀ a b, |g a b| ≤ B)
    (hlim : Tendsto (fun m =>
      ∫ a, (∫ b, (f m a b - g a b)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ a, (∫ b, (f mp.1 a b - f mp.2 a b)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by sorry
