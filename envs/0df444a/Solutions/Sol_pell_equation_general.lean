-- Prove2me | solution 1 for pell_equation_general
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T00:38:43.970052+00:00
-- url     : https://prove2.me/submissions/8b983339-a90d-4e5e-a99f-80cce00b2b6a

import Mathlib.NumberTheory.Pell

theorem solution (d : ℕ) (hd : ¬ ∃ k : ℕ, d = k ^ 2) :
    {(x, y) : ℤ × ℤ | x ^ 2 - d * y ^ 2 = 1}.Infinite := by
  have hn : ¬ IsSquare d := by simpa [IsSquare, pow_two] using hd
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => hn (by simp [h])
  have hi : ¬ IsSquare (d : ℤ) := by simpa [Int.isSquare_natCast_iff] using hn
  obtain ⟨a, ha⟩ := Pell.IsFundamental.exists_of_not_isSquare
    (d := (d : ℤ)) (by exact_mod_cast hd0) hi
  let f : ℤ → ℤ × ℤ := fun n => ((a ^ n).x, (a ^ n).y)
  have hf : Function.Injective f := by
    intro n m h
    exact ha.y_strictMono.injective (congrArg Prod.snd h)
  apply (Set.infinite_range_of_injective hf).mono
  rintro _ ⟨n, rfl⟩
  exact (a ^ n).prop

#print axioms solution
