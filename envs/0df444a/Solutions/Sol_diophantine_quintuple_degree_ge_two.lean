-- Prove2me | solution 1 for diophantine_quintuple_degree_ge_two
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T06:43:46.788179+00:00
-- url     : https://prove2.me/submissions/85add35d-1bbe-4cc4-bca3-0c379b15aeb5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_diophantine_triple_non_euler_lower_bound
import Theorems.Thm_diophantine_quintuple_acb_upper_bound
import Definitions.Def_diophantine_descent
import Theorems.Thm_diophantine_degree_ge_two_case_one_quintuple
import Theorems.Thm_diophantine_degree_ge_two_case_two_quintuple
import Theorems.Thm_diophantine_degree_ge_two_case_three_quintuple
import Theorems.Thm_diophantine_degree_ge_two_case_four_quintuple
import Theorems.Thm_diophantine_degree_ge_two_case_five_quintuple
import Theorems.Thm_diophantine_quintuple_global_bound

set_option autoImplicit false

open DiophantineDescent

/-- Direct: the three smallest entries of an ordered quintuple form a triple. -/
theorem pi_ge_two_triple_of_quintuple (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) : Triple (f 0) (f 1) (f 2) := by
  obtain ⟨hpos, _, hsq⟩ := hq
  exact ⟨hpos 0, ho.1, ho.2.1,
    hsq 0 1 (by decide), hsq 0 2 (by decide), hsq 1 2 (by decide)⟩

/-- Direct: degree `≥ 2` triples are not Euler (first descent step needs it). -/
theorem pi_ge_two_not_euler_of_degree_ge_two (a b c n : Nat)
    (hd : HasDegree a b c n) (hn : 2 ≤ n) : ¬ Euler a b c := by
  cases hd with
  | zero _ hE => omega
  | succ hS _ =>
    obtain ⟨_, hne, _, _⟩ := hS
    exact hne

/-- Direct (checked coverage helper): the five corrected intervals cover the
outer range `4*a*b < c`, `20*a*c < 3609*b^3` (Case III uses the corrected
`c² ≤ 16*a^3*b^5` from the detailed proof under label `thm:deg2`). -/
theorem pi_ge_two_interval_coverage (a b c : Nat)
    (hlo : 4 * a * b < c) (hhi : a * c * 20 < 3609 * b ^ 3) :
    (4 * a * b < c ∧ c ^ 2 ≤ 16 * a * b ^ 3) ∨
    (16 * a * b ^ 3 < c ^ 2 ∧ c ≤ 4 * a * b ^ 2) ∨
    (4 * a * b ^ 2 < c ∧ c ^ 2 ≤ 16 * a ^ 3 * b ^ 5) ∨
    (16 * a ^ 3 * b ^ 5 < c ^ 2 ∧ c ≤ 4 * a ^ 2 * b ^ 3) ∨
    (4 * a ^ 2 * b ^ 3 < c ∧ a * c * 20 < 3609 * b ^ 3) := by
  rcases Decidable.em (c ^ 2 ≤ 16 * a * b ^ 3) with h1 | h1
  · exact Or.inl ⟨hlo, h1⟩
  · have g1 : 16 * a * b ^ 3 < c ^ 2 := Nat.lt_of_not_le h1
    rcases Decidable.em (c ≤ 4 * a * b ^ 2) with h2 | h2
    · exact Or.inr (Or.inl ⟨g1, h2⟩)
    · have g2 : 4 * a * b ^ 2 < c := Nat.lt_of_not_le h2
      rcases Decidable.em (c ^ 2 ≤ 16 * a ^ 3 * b ^ 5) with h3 | h3
      · exact Or.inr (Or.inr (Or.inl ⟨g2, h3⟩))
      · have g3 : 16 * a ^ 3 * b ^ 5 < c ^ 2 := Nat.lt_of_not_le h3
        rcases Decidable.em (c ≤ 4 * a ^ 2 * b ^ 3) with h4 | h4
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨g3, h4⟩)))
        · have g4 : 4 * a ^ 2 * b ^ 3 < c := Nat.lt_of_not_le h4
          exact Or.inr (Or.inr (Or.inr (Or.inr ⟨g4, hhi⟩)))

/-- Reduction matching the exact target
`Theorems/Thm_diophantine_quintuple_degree_ge_two.lean`:
from the ordered-quintuple triple, the two tracked range bounds, the global
bound, and coverage, exactly one corrected case applies and closes the goal. -/
theorem solution (f : Fin 5 → Nat) (hq : Quintuple f)
    (ho : Ordered f) (n : Nat) (hn : 2 ≤ n)
    (hd : HasDegree (f 0) (f 1) (f 2) n) : False := by
  have hT : Triple (f 0) (f 1) (f 2) := pi_ge_two_triple_of_quintuple f hq ho
  have hne : ¬ Euler (f 0) (f 1) (f 2) :=
    pi_ge_two_not_euler_of_degree_ge_two _ _ _ n hd hn
  have hlo : 4 * f 0 * f 1 < f 2 :=
    diophantine_triple_non_euler_lower_bound _ _ _ hT hne
  have hhi : f 0 * f 2 * 20 < 3609 * f 1 ^ 3 :=
    diophantine_quintuple_acb_upper_bound f hq ho
  have hglob : f 0 * f 2 < 67700000000000000000000000 :=
    (diophantine_quintuple_global_bound f hq ho).1
  have hcov := pi_ge_two_interval_coverage (f 0) (f 1) (f 2) hlo hhi
  rcases hcov with ⟨h1lo, h1hi⟩ | ⟨h2lo, h2hi⟩ | ⟨h3lo, h3hi⟩ | ⟨h4lo, h4hi⟩ | ⟨h5lo, h5hi⟩
  · exact diophantine_degree_ge_two_case_one_quintuple _ _ _ n f hT hn hd
      hq ho rfl rfl rfl hglob h1lo h1hi
  · exact diophantine_degree_ge_two_case_two_quintuple _ _ _ n f hT hn hd
      hq ho rfl rfl rfl hglob h2lo h2hi
  · exact diophantine_degree_ge_two_case_three_quintuple _ _ _ n f hT hn hd
      hq ho rfl rfl rfl hglob h3lo h3hi
  · exact diophantine_degree_ge_two_case_four_quintuple _ _ _ n f hT hn hd
      hq ho rfl rfl rfl hglob h4lo h4hi
  · exact diophantine_degree_ge_two_case_five_quintuple _ _ _ n f hT hn hd
      hq ho rfl rfl rfl hglob h5lo h5hi

#print axioms solution
