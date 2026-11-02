-- Prove2me | solution 1 for finite_graph_property_maximal_supergraph__p2m_266b1a11_87af_4c8d_8cdc_f947960a0fd8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:05:16.20667+00:00
-- url     : https://prove2.me/submissions/55511b8b-49b3-44bf-8417-ab7438f81d3a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_finite_graph_property_maximal_supergraph_finite_max__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
import Theorems.Thm_finite_graph_property_maximal_supergraph_strict_edge_count__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (instK : DecidableRel K.Adj)
    (P : SimpleGraph V → Prop) (hK : P K) :
    Exists fun H : SimpleGraph V => Exists fun dH : DecidableRel H.Adj =>
      P H ∧
      (forall u v, K.Adj u v → H.Adj u v) ∧
      K.edgeFinset.card ≤ (by letI : DecidableRel H.Adj := dH; exact H.edgeFinset.card) ∧
      (forall J : SimpleGraph V, P J →
        (forall u v, H.Adj u v → J.Adj u v) →
        (forall u v, J.Adj u v → H.Adj u v)) := by
  classical
  obtain ⟨H, dH, hPH, hKH, hmax⟩ :=
    finite_graph_property_maximal_supergraph_finite_max__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
      K P hK
  refine ⟨H, dH, hPH, hKH, ?_, ?_⟩
  · exact hmax K instK hK (fun _ _ h => h)
  · intro J hPJ hHJ
    let dJ : DecidableRel J.Adj := Classical.decRel J.Adj
    have hKJ : ∀ x y, K.Adj x y → J.Adj x y := by
      intro x y hxy
      exact hHJ x y (hKH x y hxy)
    have hle :
        (letI : DecidableRel H.Adj := dH
         letI : DecidableRel J.Adj := dJ
         J.edgeFinset.card ≤ H.edgeFinset.card) :=
      hmax J dJ hPJ hKJ
    intro u v huv
    by_contra hnot
    have hlt :=
      finite_graph_property_maximal_supergraph_strict_edge_count__p2m_98fc4204_1185_42f8_9d24_9b96a2776006_a1
        H J dH dJ hHJ ⟨u, v, huv, hnot⟩
    exact (not_lt_of_ge hle) hlt