-- Prove2me | solution 2 for pell_equation_general
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T02:20:11.30119+00:00
-- url     : https://prove2.me/submissions/04f0d7e6-e50d-4efb-bb33-111cc69b3f37

import Mathlib.NumberTheory.Pell
import Mathlib.Data.Set.Finite.Basic

theorem solution (d : ℕ) (hd : ¬ ∃ k : ℕ, d = k ^ 2) :
    {(x, y) : ℤ × ℤ | x ^ 2 - d * y ^ 2 = 1}.Infinite := by
  have hd0 : 0 < (d : ℤ) := by
    have : d ≠ 0 := fun h => hd ⟨0, by simp [h]⟩
    exact_mod_cast Nat.pos_of_ne_zero this
  have hns : ¬ IsSquare (d : ℤ) := by
    rintro ⟨r, hr⟩
    apply hd
    refine ⟨r.natAbs, ?_⟩
    have : ((d : ℕ) : ℤ) = ((r.natAbs ^ 2 : ℕ) : ℤ) := by
      push_cast
      rw [hr, sq, abs_mul_abs_self]
    exact_mod_cast this
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare hd0 hns
  have hinj : Function.Injective (fun n : ℤ => ((a ^ n).x, (a ^ n).y)) := by
    intro m n hmn
    have := congrArg Prod.snd hmn
    exact ha.y_strictMono.injective this
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro n
  show (a ^ n).x ^ 2 - (d : ℤ) * (a ^ n).y ^ 2 = 1
  exact (a ^ n).prop
