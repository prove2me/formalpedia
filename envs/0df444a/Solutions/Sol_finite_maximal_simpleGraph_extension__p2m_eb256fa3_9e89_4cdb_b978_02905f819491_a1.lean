-- Prove2me | solution 1 for finite_maximal_simpleGraph_extension__p2m_eb256fa3_9e89_4cdb_b978_02905f819491_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:15.764207+00:00
-- url     : https://prove2.me/submissions/47187250-62c3-46ba-bc83-cfdaf5fe473b

import Mathlib
import Theorems.Thm_finite_simpleGraph_type_is_finite__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
import Theorems.Thm_finite_maximal_element_above_property__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3

open SimpleGraph

theorem solution
    {V : Type} [Fintype V]
    (H : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ P K ∧
        ∀ L : SimpleGraph V, K ≤ L → P L → L = K := by
  classical
  letI : Finite (SimpleGraph V) :=
    finite_simpleGraph_type_is_finite__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
  letI : Fintype (SimpleGraph V) := Fintype.ofFinite (SimpleGraph V)
  exact finite_maximal_element_above_property__p2m_a10335eb_4418_4032_b49f_d3c3f6c6ba7f_a3
    P H hP