-- Prove2me | solution 1 for finite_predicate_maximal_supergraph__p2m_768c520d_0a53_42aa_bcb6_e73e3939ed8f_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:41:44.028205+00:00
-- url     : https://prove2.me/submissions/96b4eecc-c2ae-4561-974a-94fd99aab38c

import Mathlib
import Theorems.Thm_finite_rel_maximal_extension__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
import Theorems.Thm_finite_simpleGraph__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (G : SimpleGraph V) (hG : P G) :
    ∃ K : SimpleGraph V, P K ∧ Set.Subset G.edgeSet K.edgeSet ∧
      (∀ H : SimpleGraph V, P H → Set.Subset K.edgeSet H.edgeSet →
        Set.Subset H.edgeSet K.edgeSet) := by
  letI : Finite (SimpleGraph V) := finite_simpleGraph__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
  let r : SimpleGraph V → SimpleGraph V → Prop := fun A B => A.edgeSet ⊆ B.edgeSet
  have hr : ∀ A : SimpleGraph V, r A A := by
    intro A
    exact Set.Subset.rfl
  have ht : ∀ A B C : SimpleGraph V, r A B → r B C → r A C := by
    intro A B C hAB hBC
    exact Set.Subset.trans hAB hBC
  have ha : ∀ A B : SimpleGraph V, r A B → r B A → A = B := by
    intro A B hAB hBA
    apply SimpleGraph.ext
    funext e
    funext f
    apply propext
    constructor
    · intro he
      have he' : Sym2.mk e f ∈ A.edgeSet := by
        simpa only [SimpleGraph.mem_edgeSet] using he
      have hb : Sym2.mk e f ∈ B.edgeSet := hAB he'
      simpa only [SimpleGraph.mem_edgeSet] using hb
    · intro he
      have he' : Sym2.mk e f ∈ B.edgeSet := by
        simpa only [SimpleGraph.mem_edgeSet] using he
      have ha' : Sym2.mk e f ∈ A.edgeSet := hBA he'
      simpa only [SimpleGraph.mem_edgeSet] using ha'
  let Q : SimpleGraph V → Prop := fun K => P K ∧ r G K
  have hQ : Q G := ⟨hG, hr G⟩
  obtain ⟨K, hK, hGK, hmax⟩ :=
    finite_rel_maximal_extension__p2m_038327fe_4daf_4028_a7aa_65aa49782279_a1
      r hr ht ha Q G hQ
  refine ⟨K, hK.1, hGK, ?_⟩
  intro H hH hKH
  exact hmax H ⟨hH, ht G K H hGK hKH⟩ hKH