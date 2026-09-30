-- Prove2me | solution 1 for n_queens_problem
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:58:29.967698+00:00
-- url     : https://prove2.me/submissions/dcdf9d27-78fd-4acb-a02f-d22e25cf1fe1

import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

private theorem half_board_placement (n : ℕ) (_hn : 1 ≤ n) :
    ∃ queens : Fin ((n + 1) / 2) → Fin n × Fin n,
      Function.Injective queens ∧
      ∀ i j, i ≠ j →
        (queens i).1 ≠ (queens j).1 ∧
        (queens i).2 ≠ (queens j).2 ∧
        (queens i).1.val + (queens i).2.val ≠ (queens j).1.val + (queens j).2.val ∧
        (queens i).1.val + (n - (queens i).2.val) ≠
          (queens j).1.val + (n - (queens j).2.val) := by
  let queens : Fin ((n + 1) / 2) → Fin n × Fin n := fun i =>
    (⟨i.val, by omega⟩, ⟨2 * i.val, by omega⟩)
  refine ⟨queens, ?_, ?_⟩
  · intro i j h
    exact Fin.ext (congrArg (fun p : Fin n × Fin n => p.1.val) h)
  · intro i j hij
    have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    dsimp [queens]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h
      exact hne (congrArg (fun x : Fin n => x.val) h)
    · intro h
      have hc := congrArg (fun x : Fin n => x.val) h
      change 2 * i.val = 2 * j.val at hc
      omega
    · omega
    · omega

theorem solution (n : ℕ) (hn : 1 ≤ n) :
    ∃ (Q : ℕ), Q ≥ 1 ∧
      ∃ (queens : Fin Q → Fin n × Fin n),
        Function.Injective queens ∧
        (∀ i j : Fin Q, i ≠ j →
          (queens i).1 ≠ (queens j).1 ∧
          (queens i).2 ≠ (queens j).2 ∧
          (queens i).1.val + (queens i).2.val ≠
            (queens j).1.val + (queens j).2.val ∧
          (queens i).1.val + (Fintype.card (Fin n) - (queens i).2.val) ≠
            (queens j).1.val + (Fintype.card (Fin n) - (queens j).2.val)) := by
  refine ⟨(n + 1) / 2, by omega, ?_⟩
  simpa only [Fintype.card_fin] using half_board_placement n hn
