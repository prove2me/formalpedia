-- Prove2me | solution 1 for mistakesFrom_init_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:43.561447+00:00
-- url     : https://prove2.me/submissions/fb9ffa2c-b6ca-44d8-983e-8b582f4a6837

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Criterion_Online
public import Mathlib.Order.Lattice.Nat
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_GameInfra

set_option autoImplicit true
@[expose] public section
public section
theorem _root_.solution {X : Type}
    (L : OnlineLearner X Bool) (c : X → Bool) (seq : List X) :
    L.mistakesFrom L.init c seq = L.mistakes c seq := by
  rfl
