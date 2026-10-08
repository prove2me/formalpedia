-- Prove2me | Theorems.Thm_BookProof_ChapterAttentionCapacity_tendsto_capacityError
-- name    : BookProof.ChapterAttentionCapacity.tendsto_capacityError
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-07T02:53:46.931971+00:00
-- url     : https://prove2.me/theorems/ad15f16e-c673-447c-8621-0c5069ed9ad7
-- title:
--   `BookProof.ChapterAttentionCapacity.tendsto_capacityError` {r C : ℝ} (hr : 0 < r) (M : ℝ) : Tendsto (fun b : ℝ => 2 * C * (M * Real.exp (-(b * r ^ 2)))) atTop (𝓝 0)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterAttentionCapacity`.
--
--   `BookProof.ChapterAttentionCapacity.tendsto_capacityError` {r C : ℝ} (hr : 0 < r) (M : ℝ) : Tendsto (fun b : ℝ => 2 * C * (M * Real.exp (-(b * r ^ 2)))) atTop (𝓝 0)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterAttentionCapacity.tendsto_capacityError`.

-- Generated from ChapterAttentionCapacity.lean — theorem BookProof.ChapterAttentionCapacity.tendsto_capacityError
import Definitions.Def_ChapterSoftmaxSharpness
import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionCapacity
open BookProof.ChapterAttentionCapacity


open scoped BigOperators

open Filter Topology

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem BookProof.ChapterAttentionCapacity.tendsto_capacityError {r C : ℝ} (hr : 0 < r) (M : ℝ) :
    Tendsto (fun b : ℝ => 2 * C * (M * Real.exp (-(b * r ^ 2)))) atTop (𝓝 0) := by sorry
