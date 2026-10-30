-- Prove2me | solution 1 for finite_simpleGraph_maximal_supergraph__p2m_8526028d_6503_4baf_b95b_7d2634d3c3de_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:28:26.835899+00:00
-- url     : https://prove2.me/submissions/ff0180ab-91cc-452d-96c6-8e21f9bb047b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V] (P : SimpleGraph V → Prop)
    (L : SimpleGraph V) (hL : P L) :
    ∃ K : SimpleGraph V, L ≤ K ∧ P K ∧ (∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K) := by
  classical
  let S : Set (SimpleGraph V) := {K | L ≤ K ∧ P K}
  have hSfinite : S.Finite := Set.toFinite S
  have hSnonempty : S.Nonempty := ⟨L, le_rfl, hL⟩
  obtain ⟨K, hKmax⟩ := hSfinite.exists_maximal hSnonempty
  have hKmem : K ∈ S := hKmax.1
  have hKmaximal : ∀ H, H ∈ S → K ≤ H → H ≤ K := hKmax.2
  refine ⟨K, hKmem.1, hKmem.2, ?_⟩
  intro H hKH hPH
  apply hKmaximal H
  · exact ⟨hKmem.1.trans hKH, hPH⟩
  · exact hKH