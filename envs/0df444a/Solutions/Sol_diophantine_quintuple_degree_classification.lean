-- Prove2me | solution 1 for diophantine_quintuple_degree_classification
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-09-07T02:49:57.491188+00:00
-- url     : https://prove2.me/submissions/f0898389-dc30-4782-b656-b29f2ebcdc64

import Theorems.Thm_diophantine_quintuple_sorting
import Theorems.Thm_diophantine_triple_finite_degree
import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem solution (f : Fin 5 → Nat) (hq : Quintuple f) :
    ∃ g : Fin 5 → Nat, Quintuple g ∧ Ordered g ∧
      (∀ i, ∃ j, g i = f j) ∧ ∃ n : Nat, HasDegree (g 0) (g 1) (g 2) n := by
  obtain ⟨g, hg, ho, himg⟩ := diophantine_quintuple_sorting f hq
  obtain ⟨hpos, hinj, hsq⟩ := hg
  have hT : Triple (g 0) (g 1) (g 2) :=
    ⟨hpos 0, ho.1, ho.2.1,
     hsq 0 1 (by decide), hsq 0 2 (by decide), hsq 1 2 (by decide)⟩
  obtain ⟨n, hn⟩ := diophantine_triple_finite_degree _ _ _ hT
  exact ⟨g, ⟨hpos, hinj, hsq⟩, ho, himg, n, hn⟩
