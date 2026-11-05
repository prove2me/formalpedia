-- Prove2me | solution 1 for finite_simpleGraph_maximal_supergraph__p2m_1841e8f3_3dc0_4413_8d65_8f642645b455_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:20:24.732133+00:00
-- url     : https://prove2.me/submissions/98672221-b5d4-4b41-90f5-a2cf1d0c9772

import Mathlib

set_option linter.unusedVariables false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (P : SimpleGraph V → Prop) (hP : P G)
    (hP_super : ∀ K : SimpleGraph V, LE.le G K → P K) :
    Exists fun K : SimpleGraph V => And (LE.le G K)
      (And (P K) (∀ L : SimpleGraph V, LE.le K L → P L → LE.le L K)) := by
  refine ⟨⊤, le_top, hP_super ⊤ le_top, ?_⟩
  intro L hTL hPL
  exact le_top
