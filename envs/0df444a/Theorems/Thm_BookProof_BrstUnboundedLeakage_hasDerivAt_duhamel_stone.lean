-- Prove2me | Theorems.Thm_BookProof_BrstUnboundedLeakage_hasDerivAt_duhamel_stone
-- name    : BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-07T21:18:15.727034+00:00
-- url     : https://prove2.me/theorems/f0fb7de9-514e-4e26-9466-3306a2ae091f
-- title:
--   `BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone` (B : H →L[ℂ] H) (t : ℝ) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (s : ℝ) : HasDerivAt (fun u : ℝ => T.stoneU (t - u
-- statement:
--   Prove the following Lean 4 theorem from `ChapterBrstUnboundedLeakage`.
--
--   `BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone` (B : H →L[ℂ] H) (t : ℝ) (x : H) (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (s : ℝ) : HasDerivAt (fun u : ℝ => T.stoneU (t - u) (flow B u x)) (T.stoneU (t - s) ((-Complex.I) • (B (flow B s x) - T.op ⟨flow B s x, hdom s⟩))) s
--
--   Formalization note: Lean 4 identifier `BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone`.

-- Generated from ChapterBrstUnboundedLeakage.lean — theorem BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone
import Definitions.Def_ChapterSirkTrotterKato
import Mathlib
import Definitions.Def_ChapterBrstUnboundedLeakage
import Definitions.Def_ChapterBrstTruncationLeakage
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterStoneUnitary
open BookProof.BrstLeakage
open BookProof.BrstUnboundedLeakage


open NormedSpace Filter Topology
open scoped InnerProductSpace


open BookProof.BrstLeakage BookProof.ChapterStoneResolvent

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (T : UnboundedSelfAdjoint H)

theorem BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone (B : H →L[ℂ] H) (t : ℝ) (x : H)
    (hdom : ∀ s : ℝ, flow B s x ∈ T.domain) (s : ℝ) :
    HasDerivAt (fun u : ℝ => T.stoneU (t - u) (flow B u x))
      (T.stoneU (t - s) ((-Complex.I) • (B (flow B s x) - T.op ⟨flow B s x, hdom s⟩))) s := by sorry
