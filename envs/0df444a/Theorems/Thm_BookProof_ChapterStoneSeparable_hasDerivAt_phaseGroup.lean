-- Prove2me | Theorems.Thm_BookProof_ChapterStoneSeparable_hasDerivAt_phaseGroup
-- name    : BookProof.ChapterStoneSeparable.hasDerivAt_phaseGroup
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-20T05:01:41.297044+00:00
-- url     : https://prove2.me/theorems/97b6911b-e778-4153-a474-bc178c4245c1
-- title:
--   `BookProof.ChapterStoneSeparable.hasDerivAt_phaseGroup` (f : ℤ → ℝ) (x : (mulSA f).domain) : HasDerivAt (fun t : ℝ => (phaseGroup f).U t (x : L2Z)) ((-Complex.I) • (mulSA f).op x)
-- statement:
--   Prove the following Lean 4 theorem from `ChapterStoneSeparable`.
--
--   `BookProof.ChapterStoneSeparable.hasDerivAt_phaseGroup` (f : ℤ → ℝ) (x : (mulSA f).domain) : HasDerivAt (fun t : ℝ => (phaseGroup f).U t (x : L2Z)) ((-Complex.I) • (mulSA f).op x) 0
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterStoneSeparable.hasDerivAt_phaseGroup`.

-- Generated from ChapterStoneSeparable.lean — theorem BookProof.ChapterStoneSeparable.hasDerivAt_phaseGroup
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterStoneConverse
import Mathlib
import Definitions.Def_ChapterStoneSeparable
import Definitions.Def_ChapterContinuityUnitaryInfinite
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterUnboundedPosition
open BookProof.ChapterContinuityUnitaryInfinite
open BookProof.ChapterF7
open BookProof.ChapterUnboundedPosition
open BookProof.ChapterStoneSeparable


open scoped InnerProductSpace
open Filter Topology


open BookProof.ChapterStoneResolvent BookProof.ChapterStoneMeasurable

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

theorem BookProof.ChapterStoneSeparable.hasDerivAt_phaseGroup (f : ℤ → ℝ) (x : (mulSA f).domain) :
    HasDerivAt (fun t : ℝ => (phaseGroup f).U t (x : L2Z))
      ((-Complex.I) • (mulSA f).op x) 0 := by sorry
