-- Prove2me | Theorems.Thm_CompleteParityWidth_explicit_complete_parity_family
-- name    : CompleteParityWidth.explicit_complete_parity_family
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T21:29:04.130051+00:00
-- url     : https://prove2.me/theorems/1d97fc42-0510-4112-ad15-8dbd0428816d
-- title:
--   Quadratic resolution width for complete-graph parity contradictions
-- statement:
--   For each n at least three, put charge one on vertex zero and charge zero on the other vertices of the complete graph with both orientations as separately labelled edges. The parity CNF is unsatisfiable, has at most n times 2 to the 2n clauses, and every input clause has at most 2n literals. Every resolution refutation with weakening has a clause of width at least the square of the floor of n divided by three.
-- source:
--   The balanced-support and boundary argument for Tseitin contradictions. See Ben-Sasson and Wigderson, Short Proofs Are Narrow, JACM 48(2), 2001, Sections 4.1 and 6.1.

import Definitions.Def_CompleteParityWidth

open CompleteParityWidth

theorem CompleteParityWidth.explicit_complete_parity_family (n : ℕ) (enough : 3 ≤ n) :
    let charge : Fin n → Bit := oneCharge ⟨0,by omega⟩
    let F := parityCNF charge
    (¬ ∃ x, ∀ C ∈ F, Holds x C) ∧ F.card ≤ n * 2^(2*n) ∧
      (∀ C ∈ F, C.card ≤ 2*n) ∧
      ∀ w, BoundedResolution F w ∅ → (n/3)*(n/3) ≤ w := by sorry
