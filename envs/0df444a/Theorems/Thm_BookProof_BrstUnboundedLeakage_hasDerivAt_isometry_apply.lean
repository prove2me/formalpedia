-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_hasDerivAt_isometry_apply
-- name    : BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:17:44.364+00:00
-- url     : https://prove2.me/theorems/3784ecab-ca01-49f9-9237-6e8405b6202c
-- title:
--   `BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply` {U : ℝ → H →L[ℂ] H} {f : ℝ → H} {f' : H} (hiso : ∀ (h : ℝ) (y : H), ‖U h y‖ = ‖y‖) (hU0 : ∀ y : H, U 0 y = y)...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply` {U : ℝ → H →L[ℂ] H} {f : ℝ → H} {f' : H} (hiso : ∀ (h : ℝ) (y : H), ‖U h y‖ = ‖y‖) (hU0 : ∀ y : H, U 0 y = y) (hcont : ∀ y : H, Tendsto (fun h : ℝ => U h y) (𝓝 0) (𝓝 y)) (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0) : HasDerivAt (fun h : ℝ => U h (f h)) f' 0
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply {U : ℝ → H →L[ℂ] H} {f : ℝ → H} {f' : H}
    (hiso : ∀ (h : ℝ) (y : H), ‖U h y‖ = ‖y‖) (hU0 : ∀ y : H, U 0 y = y)
    (hcont : ∀ y : H, Tendsto (fun h : ℝ => U h y) (𝓝 0) (𝓝 y))
    (hf : HasDerivAt f f' 0) (hf0 : f 0 = 0) :
    HasDerivAt (fun h : ℝ => U h (f h)) f' 0 := by sorry
