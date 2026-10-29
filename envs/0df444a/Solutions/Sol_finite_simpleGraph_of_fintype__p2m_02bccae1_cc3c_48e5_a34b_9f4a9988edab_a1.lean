-- Prove2me | solution 1 for finite_simpleGraph_of_fintype__p2m_02bccae1_cc3c_48e5_a34b_9f4a9988edab_a1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T21:04:43.001778+00:00
-- url     : https://prove2.me/submissions/ed01fcfb-8647-4a59-9852-1ce6d827c137

import Mathlib

theorem solution (V : Type) [Fintype V] : Finite (SimpleGraph V) :=
  Finite.of_injective (fun G : SimpleGraph V => G.Adj) (fun _ _ h => SimpleGraph.ext h)
