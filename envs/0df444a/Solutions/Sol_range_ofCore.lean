-- Prove2me | solution 1 for range_ofCore
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T18:10:05.890182+00:00
-- url     : https://prove2.me/submissions/771068a9-49c3-47df-9583-7adf3b058d87

-- Generated from ChapterPaFreeCompletion.lean — solution of range_ofCore
import Mathlib
import Definitions.Def_ChapterPaFreeCompletion
import Definitions.Def_ChapterRieszFischer
import Definitions.Def_ChapterA4



open Set
open Filter
open BookProof.ChapterRieszFischer


@[simp] private theorem ofCore_apply (v : DenseCore) (j : ℕ) : (ofCore v : ℕ → ℝ) j = v j := by
  rw [ofCore, lp.coeFn_sum]
  simp only [Finset.sum_apply, lp.single_apply, Pi.single_apply, Finset.sum_ite_eq]
  by_cases hj : j ∈ v.support
  · simp [hj]
  · rw [if_neg hj, (Finsupp.notMem_support_iff).mp hj]

set_option maxHeartbeats 1000000 in
theorem solution : Set.range ofCore = FinSupport := by

  ext f
  constructor
  · rintro ⟨v, rfl⟩
    refine Set.Finite.subset (v.support.finite_toSet) ?_
    intro j hj
    simp only [Function.mem_support, ofCore_apply] at hj
    simpa using Finsupp.mem_support_iff.mpr hj
  · intro hf
    simp only [FinSupport, Set.mem_setOf_eq] at hf
    refine ⟨Finsupp.onFinset hf.toFinset (fun n => (f : ℕ → ℝ) n) ?_, ?_⟩
    · intro n hn
      simpa using hn
    · exact Subtype.ext (funext fun j => by simp)
