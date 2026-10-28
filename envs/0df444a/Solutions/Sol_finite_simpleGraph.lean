-- Prove2me | solution 1 for finite_simpleGraph
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T06:37:30.554656+00:00
-- url     : https://prove2.me/submissions/67624c49-b514-44d1-a5f9-1041de094395

import Mathlib

set_option autoImplicit false
theorem solution
    (V : Type) [Fintype V] :
    Finite (SimpleGraph V) := by
  classical
  infer_instance
