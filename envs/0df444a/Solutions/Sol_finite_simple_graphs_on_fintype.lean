-- Prove2me | solution 1 for finite_simple_graphs_on_fintype
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T19:00:53.788296+00:00
-- url     : https://prove2.me/submissions/6844200f-98c2-49a3-b52d-44899e6487a3

import Mathlib
theorem solution (V : Type) [Fintype V] : Finite (SimpleGraph V) := by
  classical
  infer_instance
