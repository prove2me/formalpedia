-- Prove2me | Theorems.Thm_DetDLP_d4b_three_oracle_mux
-- name    : DetDLP.d4b_three_oracle_mux
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T07:45:27.427728+00:00
-- url     : https://prove2.me/theorems/79aefe72-1ea2-4b7a-a577-94798b6d027c
-- title:
--   Tagged three-oracle dispatch machine
-- statement:
--   A fixed tagged dispatcher combines three machines into one machine. The tag directs an input to one of three branches, and each branch preserves the output while the combined machine has polynomially bounded time and visited space.
-- source:
--   Uniform tagged dispatch of three primitive machines; uses the resettable-machine normalization and tape relocation.

import Definitions.Def_DetDLP_W1_Pipeline
import Theorems.Thm_DetDLP_m89_resettable_machine
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace DetDLP DetDLP.MachineComposition

theorem DetDLP.d4b_three_oracle_mux (A : Fin 3 → PrimitiveMachine) (o : ∀ j, Fin (A j).tapeCount) :
    ∃ (M : PrimitiveMachine) (K : ℕ), ∀ (j : Fin 3) (x y : List Bool) (t s : ℝ),
      RunsWithin (A j) (o j) x y t s →
      RunsWithin M M.inputTape (if j = 0 then false :: x else true :: decide (j = 2) :: x) y
        (K * (t + x.length + 1)) (K * (s + x.length + 1)) := by sorry
