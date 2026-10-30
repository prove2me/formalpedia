-- Prove2me | solution 1 for finite_maximal_simpleGraph_extension__p2m_7fd45cf3_e203_47de_9dbd_2f0909dacdf1_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:20:28.216278+00:00
-- url     : https://prove2.me/submissions/a2963f2c-1104-4c14-9c9e-f55182a9c005

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (L : SimpleGraph V) (hP : P L) :
    ∃ M : SimpleGraph V,
      LE.le L M ∧ P M ∧
        ∀ N : SimpleGraph V, P N → LE.le M N → LE.le N M := by
  classical
  let S : Set (SimpleGraph V) := {G | P G ∧ L ≤ G}
  have hS : S.Finite := Set.toFinite S
  have hne : S.Nonempty := ⟨L, hP, le_rfl⟩
  obtain ⟨M, hM, hmax⟩ := hS.exists_maximal hne
  change P M ∧ L ≤ M at hM
  refine ⟨M, hM.2, hM.1, ?_⟩
  intro N hPN hMN
  exact hmax ⟨hPN, hM.2.trans hMN⟩ hMN