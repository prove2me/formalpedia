-- Prove2me | solution 1 for exists_edge_maximal_supergraph_for_finite_predicate__p2m_4cf1e2b2_149e_4f7a_8404_753e093946ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:40.054925+00:00
-- url     : https://prove2.me/submissions/44f176fa-a655-4841-82c2-d177860a59bd

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (R : SimpleGraph V → Prop)
    (M : SimpleGraph V)
    (hM : R M) :
    ∃ N : SimpleGraph V,
      R N ∧
      (∀ u v, M.Adj u v → N.Adj u v) ∧
      (∀ P : SimpleGraph V,
        R P →
        (∀ u v, M.Adj u v → P.Adj u v) →
        (∀ u v, N.Adj u v → P.Adj u v) →
        P = N) := by
  classical
  let admissible : Finset (SimpleGraph V) :=
    Finset.univ.filter
      (fun G => R G ∧ ∀ u v, M.Adj u v → G.Adj u v)
  have hadmissible : admissible.Nonempty := by
    refine ⟨M, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact ⟨hM, fun _ _ h => h⟩
  let edgePairs : SimpleGraph V → Finset (V × V) :=
    fun G => Finset.univ.filter (fun p => G.Adj p.1 p.2)
  obtain ⟨N, hNmem, hNmax⟩ :=
    Finset.exists_max_image admissible
      (fun G => (edgePairs G).card) hadmissible
  have hNprops : R N ∧ ∀ u v, M.Adj u v → N.Adj u v := by
    simpa [admissible] using hNmem
  refine ⟨N, hNprops.1, hNprops.2, ?_⟩
  intro P hP hMP hNP
  have hPmem : P ∈ admissible := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hP, hMP⟩⟩
  by_contra hPN
  have hneq : edgePairs N ≠ edgePairs P := by
    intro heq
    apply hPN
    ext u v
    have hmem := congrArg (fun s : Finset (V × V) => (u, v) ∈ s) heq
    exact (Iff.of_eq (by simpa [edgePairs] using hmem)).symm
  have hsubset : edgePairs N ⊂ edgePairs P := by
    apply Finset.ssubset_iff_subset_ne.mpr
    constructor
    · intro x hx
      have hx' : N.Adj x.1 x.2 := by
        simpa [edgePairs] using hx
      simpa [edgePairs] using hNP x.1 x.2 hx'
    · exact hneq
  have hcard : (edgePairs N).card < (edgePairs P).card :=
    Finset.card_lt_card hsubset
  have hmax := hNmax P hPmem
  dsimp [edgePairs] at hmax hcard
  omega
