-- Prove2me | solution 1 for d9_hasDerivWithinAt_sub_const_left
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T18:42:37.160001+00:00
-- url     : https://prove2.me/submissions/cf304db5-c443-4bc4-a3b8-7e94f6a36981

-- ID: 7a2379b7-5e13-4748-bc1f-5d14fe412c5f | NAME: d9_hasDerivWithinAt_sub_const_left | 未本地编译验证
import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
open NestedSeatAlloc.IntPolicy

theorem solution
    (g : ℝ → ℝ) (s x d : ℝ)
    (hg : HasDerivWithinAt g d (Set.Iic (s - x)) (s - x)) :
    HasDerivWithinAt (fun t => g (t - x)) d (Set.Iic s) s := by
  have hf : HasDerivWithinAt (fun t : ℝ => t - x) 1 (Set.Iic s) s := by
    simpa using
      (hasDerivWithinAt_id (𝕜 := ℝ) (s := Set.Iic s) (x := s)).sub_const x
  have hmaps : Set.MapsTo (fun t : ℝ => t - x) (Set.Iic s) (Set.Iic (s - x)) := by
    intro t ht
    simp only [Set.mem_Iic] at ht ⊢
    linarith
  simpa [Function.comp_def] using hg.comp s hf hmaps
