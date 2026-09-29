-- Prove2me | solution 1 for mme_CW_2376_vertex_closed_target_pruning_assembles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:21:10.252425+00:00
-- url     : https://prove2.me/submissions/2125fa9c-83a9-49de-9cda-5507e5c667ee

import Definitions.Def_mme_CW_2376_marginal_hash_state
import Theorems.Thm_mme_tripartite_target_isolation_pruning

open MME

set_option autoImplicit false

/-- A vertex-closed retained part of the full marginal hypergraph, together
with target-relative collision deletion, produces an honestly induced family
of exact-profile addresses. -/
theorem solution
    (m : ℕ) (E : Finset (CW2376MarginalSupportedAddress m))
    (hclosed : CW2376MarginalVertexClosed E) :
    ∃ G : Finset (CW2376ExactProfileAddress m),
      CW2376InducedModeDisjoint G ∧
      ((cw2376ExactTargetEdges E).card : ℝ) ≤
        (G.card : ℝ) + (cw2376TargetAmbientCollisions E).card := by
  classical
  let T := cw2376ExactTargetEdges E
  let v : ∀ i : Fin 3,
      CW2376MarginalSupportedAddress m →
        (Fin (cw2376ProfileLength m) → Fin 5) :=
    fun i e => e.1 i
  have hTE : T ⊆ E := by
    intro e he
    exact (Finset.mem_filter.mp (show e ∈ cw2376ExactTargetEdges E from he)).1
  obtain ⟨F, hFT, hdisjoint, hinduced, hcard⟩ :=
    mme_tripartite_target_isolation_pruning v E T hTE
  let liftExact : ↑F → CW2376ExactProfileAddress m := fun e =>
    ⟨e.1.1, (Finset.mem_filter.mp
      (show e.1 ∈ cw2376ExactTargetEdges E from hFT e.2)).2⟩
  have hlift_injective : Function.Injective liftExact := by
    intro x y hxy
    have hbase : (liftExact x).1 = (liftExact y).1 :=
      congrArg (fun q : CW2376ExactProfileAddress m => q.1) hxy
    exact Subtype.ext (Subtype.ext hbase)
  let G : Finset (CW2376ExactProfileAddress m) :=
    F.attach.image liftExact
  have hcardG : G.card = F.card := by
    calc
      G.card = F.attach.card := by
        exact Finset.card_image_of_injective F.attach hlift_injective
      _ = F.card := Finset.card_attach
  refine ⟨G, ?_, ?_⟩
  · constructor
    · intro x y hxy i hsame
      obtain ⟨ux, _, hux⟩ := Finset.mem_image.mp x.2
      obtain ⟨uy, _, huy⟩ := Finset.mem_image.mp y.2
      have hraw_ne : ux.1 ≠ uy.1 := by
        intro h
        apply hxy
        apply Subtype.ext
        exact hux.symm.trans ((congrArg liftExact (Subtype.ext h)).trans huy)
      apply hdisjoint ux.1 ux.2 uy.1 uy.2 hraw_ne i
      have hxbase : ux.1.1 = x.1.1 := congrArg Subtype.val hux
      have hybase : uy.1.1 = y.1.1 := congrArg Subtype.val huy
      change ux.1.1 i = uy.1.1 i
      rw [hxbase, hybase]
      exact hsame
    · intro x y z hsupported
      obtain ⟨ux, _, hux⟩ := Finset.mem_image.mp x.2
      obtain ⟨uy, _, huy⟩ := Finset.mem_image.mp y.2
      obtain ⟨uz, _, huz⟩ := Finset.mem_image.mp z.2
      have hxbase : ux.1.1 = x.1.1 := congrArg Subtype.val hux
      have hybase : uy.1.1 = y.1.1 := congrArg Subtype.val huy
      have hzbase : uz.1.1 = z.1.1 := congrArg Subtype.val huz
      have hmixed :
          cw2376MixedAddress ux.1.1 uy.1.1 uz.1.1 =
            cw2376MixedAddress x.1.1 y.1.1 z.1.1 := by
        rw [hxbase, hybase, hzbase]
      have hsupportedRaw : CW2376CoordinatewiseSupported
          (cw2376MixedAddress ux.1.1 uy.1.1 uz.1.1) := by
        rw [hmixed]
        exact hsupported
      obtain ⟨e, heE, hebase⟩ :=
        hclosed ux.1 (hTE (hFT ux.2))
          uy.1 (hTE (hFT uy.2)) uz.1 (hTE (hFT uz.2)) hsupportedRaw
      have heF : e ∈ F := by
        apply hinduced e heE
        intro i
        fin_cases i
        · refine ⟨ux.1, ux.2, ?_⟩
          simpa [v, hebase, cw2376MixedAddress]
        · refine ⟨uy.1, uy.2, ?_⟩
          simpa [v, hebase, cw2376MixedAddress]
        · refine ⟨uz.1, uz.2, ?_⟩
          simpa [v, hebase, cw2376MixedAddress]
      have heq_x : e = ux.1 := by
        by_contra hne
        apply hdisjoint e heF ux.1 ux.2 hne (0 : Fin 3)
        simpa [v, hebase, cw2376MixedAddress]
      have heq_y : e = uy.1 := by
        by_contra hne
        apply hdisjoint e heF uy.1 uy.2 hne (1 : Fin 3)
        simpa [v, hebase, cw2376MixedAddress]
      have heq_z : e = uz.1 := by
        by_contra hne
        apply hdisjoint e heF uz.1 uz.2 hne (2 : Fin 3)
        simpa [v, hebase, cw2376MixedAddress]
      have hxyExact : x.1 = y.1 := by
        exact hux.symm.trans
          ((congrArg liftExact (Subtype.ext (heq_x.symm.trans heq_y))).trans huy)
      have hyzExact : y.1 = z.1 := by
        exact huy.symm.trans
          ((congrArg liftExact (Subtype.ext (heq_y.symm.trans heq_z))).trans huz)
      exact ⟨Subtype.ext hxyExact, Subtype.ext hyzExact⟩
  · have hcardReal : (T.card : ℝ) ≤
        (F.card : ℝ) +
          (((T ×ˢ E).filter (fun p =>
            p.1 ≠ p.2 ∧ ∃ i : Fin 3, v i p.1 = v i p.2)).card : ℝ) := by
      exact_mod_cast hcard
    simpa only [T, v, cw2376TargetAmbientCollisions, hcardG] using hcardReal
