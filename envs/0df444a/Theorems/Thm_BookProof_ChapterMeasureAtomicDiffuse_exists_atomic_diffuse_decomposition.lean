-- Prove2me | Theorems.Thm_BookProof_ChapterMeasureAtomicDiffuse_exists_atomic_diffuse_decomposition
-- name    : BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T13:02:30.075984+00:00
-- url     : https://prove2.me/theorems/a2b72173-b3aa-4d21-96ac-642d3a81aa46
-- title:
--   `BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition` [IsFiniteMeasure mu] : ∃ (A : Set α) (mua mud : Measure α), A.Countable ∧ MeasurableSet A ∧ mu = mua + m
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMeasureAtomicDiffuse`.
--
--   `BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition` [IsFiniteMeasure mu] : ∃ (A : Set α) (mua mud : Measure α), A.Countable ∧ MeasurableSet A ∧ mu = mua + mud ∧ mua = Measure.sum (fun x : A => mu {(x : α)} • Measure.dirac (x : α)) ∧ mua Aᶜ = 0 ∧ NullSingletonClass mud
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition`.

-- Generated from ChapterMeasureAtomicDiffuse.lean — theorem BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition
import Mathlib
import Definitions.Def_ChapterMeasureAtomicDiffuse
open BookProof.ChapterMeasureAtomicDiffuse


noncomputable section

open MeasureTheory Complex



variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α] (mu : Measure α)

theorem BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition [IsFiniteMeasure mu] :
    ∃ (A : Set α) (mua mud : Measure α), A.Countable ∧ MeasurableSet A ∧
      mu = mua + mud ∧
      mua = Measure.sum (fun x : A => mu {(x : α)} • Measure.dirac (x : α)) ∧
      mua Aᶜ = 0 ∧ NullSingletonClass mud := by sorry
