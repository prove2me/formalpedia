-- Prove2me | solution 1 for image_Ico_eq_range_of_periodic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:30:18.501227+00:00
-- url     : https://prove2.me/submissions/902d4647-60bd-407e-990f-cbda9bb92f6f

import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveGlobal
import Definitions.Def_Operator_Crouzeix_SmoothSupportCurveRange

set_option autoImplicit false
open Complex Metric Set
open scoped ContDiff
theorem _root_.solution
    {α : Type*} {f : ℝ → α} {p : ℝ}
    (hp : Function.Periodic f p) (hp_pos : 0 < p) (a : ℝ) :
    f '' Ico a (a + p) = range f := by
  apply Subset.antisymm (image_subset_range f _)
  rintro z ⟨x, rfl⟩
  obtain ⟨y, hy, hxy⟩ := hp.exists_mem_Ico hp_pos x a
  exact ⟨y, hy, hxy.symm⟩
