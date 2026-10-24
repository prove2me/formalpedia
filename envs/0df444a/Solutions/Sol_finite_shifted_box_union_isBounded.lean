-- Prove2me | solution 1 for finite_shifted_box_union_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:07:38.772648+00:00
-- url     : https://prove2.me/submissions/25e5e99e-46ff-4adb-9049-2ee70a9a1539

import Mathlib

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι]
    (n : Nat) (s : Finset ι) (a : ι → Fin n → Nat) :
    Bornology.IsBounded
      (⋃ j ∈ (s : Set ι),
        {x : Fin n → Real | ∀ i, (a j i : Real) ≤ x i ∧ x i < (a j i : Real) + 1}) := by
  refine (Bornology.isBounded_biUnion s.finite_toSet).2 (fun j _ => ?_)
  refine (Metric.isBounded_Icc (fun i => (a j i : ℝ)) (fun i => (a j i : ℝ) + 1)).subset ?_
  intro x hx
  exact ⟨fun i => (hx i).1, fun i => (hx i).2.le⟩
