-- Prove2me | solution 1 for erdos_szekeres_asymmetric_graph_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-26T13:01:35.972295+00:00
-- url     : https://prove2.me/submissions/354fe67f-620f-4675-a5df-002fce00a243

import Mathlib

theorem solution (k l : ℕ) (hk : 1 ≤ k) (hl : 1 ≤ l) :
    ∀ G : SimpleGraph (Fin (Nat.choose (k + l - 2) (k - 1))),
      (∃ s : Finset (Fin (Nat.choose (k + l - 2) (k - 1))), G.IsNClique k s) ∨
      (∃ s : Finset (Fin (Nat.choose (k + l - 2) (k - 1))), Gᶜ.IsNClique l s) := by
  classical
  have hmain : ∀ m k l, k + l = m → 1 ≤ k → 1 ≤ l →
      ∀ G : SimpleGraph (Fin (Nat.choose (k + l - 2) (k - 1))),
        (∃ s : Finset (Fin (Nat.choose (k + l - 2) (k - 1))), G.IsNClique k s) ∨
        (∃ s : Finset (Fin (Nat.choose (k + l - 2) (k - 1))), Gᶜ.IsNClique l s) := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro k l hsum hk hl G
      by_cases hk1 : k = 1
      · subst k
        have harg : 1 + l - 2 = l - 1 := by omega
        have hN : Nat.choose (1 + l - 2) (1 - 1) = 1 := by simp [harg]
        haveI : Subsingleton (Fin (Nat.choose (1 + l - 2) (1 - 1))) := by rw [hN]; infer_instance
        left
        refine ⟨Finset.univ, ?_⟩
        rw [SimpleGraph.isNClique_iff]
        constructor
        · rw [SimpleGraph.isClique_iff]
          intro x hx y hy hxy
          exact (hxy (Subsingleton.elim x y)).elim
        · simp [hN]
      by_cases hl1 : l = 1
      · subst l
        have harg : k + 1 - 2 = k - 1 := by omega
        have hN : Nat.choose (k + 1 - 2) (k - 1) = 1 := by simp [harg]
        haveI : Subsingleton (Fin (Nat.choose (k + 1 - 2) (k - 1))) := by rw [hN]; infer_instance
        right
        refine ⟨Finset.univ, ?_⟩
        rw [SimpleGraph.isNClique_iff]
        constructor
        · rw [SimpleGraph.isClique_iff]
          intro x hx y hy hxy
          exact (hxy (Subsingleton.elim x y)).elim
        · simp [hN]
      have hk' : 1 < k := by omega
      have hl' : 1 < l := by omega
      let A := Nat.choose (k - 1 + l - 2) (k - 1 - 1)
      let B := Nat.choose (k + (l - 1) - 2) (k - 1)
      have htopA : k - 1 + l - 2 = k + l - 3 := by omega
      have hlowA : k - 1 - 1 = k - 2 := by omega
      have htopB : k + (l - 1) - 2 = k + l - 3 := by omega
      have htop : k + l - 2 = (k + l - 3) + 1 := by omega
      have hlow : k - 1 = (k - 2) + 1 := by omega
      have hAB : A + B = Nat.choose (k + l - 2) (k - 1) := by
        dsimp [A, B]
        rw [htopA, hlowA, htopB, htop, hlow]
        exact Nat.choose_succ_succ (k + l - 3) (k - 2)
      have hrecA : ∀ H : SimpleGraph (Fin A),
          (∃ s : Finset (Fin A), H.IsNClique (k - 1) s) ∨
          (∃ s : Finset (Fin A), Hᶜ.IsNClique l s) := by
        intro H
        exact ih (k - 1 + l) (by omega) (k - 1) l (by omega) (by omega) hl H
      have hrecB : ∀ H : SimpleGraph (Fin B),
          (∃ s : Finset (Fin B), H.IsNClique k s) ∨
          (∃ s : Finset (Fin B), Hᶜ.IsNClique (l - 1) s) := by
        intro H
        exact ih (k + (l - 1)) (by omega) k (l - 1) (by omega) hk (by omega) H
      let v : Fin (Nat.choose (k + l - 2) (k - 1)) := ⟨0, by
        have hnpos : 0 < Nat.choose (k + l - 2) (k - 1) := by
          apply Nat.choose_pos
          omega
        omega⟩
      let V : Finset (Fin (Nat.choose (k + l - 2) (k - 1))) := Finset.univ.erase v
      let S := V.filter fun x => G.Adj v x
      let T := V.filter fun x => ¬ G.Adj v x
      have hV : V.card = Nat.choose (k + l - 2) (k - 1) - 1 := by simp [V, v]
      have hST : S.card + T.card = V.card := by
        rw [← Finset.card_filter_add_card_filter_not (s := V) (p := fun x => G.Adj v x)]

      by_cases hS : A ≤ S.card
      · obtain ⟨U, hUS, hUcard⟩ := Finset.exists_subset_card_eq hS
        let e : Fin A ↪ Fin (Nat.choose (k + l - 2) (k - 1)) := (U.orderEmbOfFin hUcard).toEmbedding
        let H : SimpleGraph (Fin A) := G.comap e
        rcases hrecA H with h | h
        · rcases h with ⟨s, hs⟩
          rw [SimpleGraph.isNClique_iff] at hs
          let u := s.map e
          have hucl : G.IsClique u := by
            have hm := hs.1.finsetMap (f := e)
            exact hm.mono (SimpleGraph.map_comap_le e G)
          have hucard : u.card = k - 1 := by simp [u, hs.2]
          have huS : ∀ x ∈ u, x ∈ S := by
            intro x hx
            rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hyU : e y ∈ U := by simpa [e] using Finset.orderEmbOfFin_mem U hUcard y
            exact hUS hyU
          have huv : v ∉ u := by
            intro hvu
            have hvS : v ∈ S := huS v hvu
            have hvV : v ∈ V := (Finset.mem_filter.mp hvS).1
            simpa [V] using hvV
          refine Or.inl ⟨insert v u, ?_⟩
          rw [SimpleGraph.isNClique_iff]
          constructor
          · rw [SimpleGraph.isClique_iff]
            intro x hx y hy hxy
            rcases Finset.mem_insert.mp hx with rfl | hx
            · rcases Finset.mem_insert.mp hy with rfl | hy
              · exact (hxy rfl).elim
              · exact (Finset.mem_filter.mp (huS y hy)).2
            · rcases Finset.mem_insert.mp hy with rfl | hy
              · exact ((Finset.mem_filter.mp (huS x hx)).2).symm
              · exact hucl hx hy hxy
          · rw [Finset.card_insert_of_notMem huv, hucard]
            omega
        · rcases h with ⟨s, hs⟩
          rw [SimpleGraph.isNClique_iff] at hs
          let u := s.map e
          have hucl : Gᶜ.IsClique u := by
            have hm := hs.1.finsetMap (f := e)
            have hEq : (G.comap e)ᶜ = Gᶜ.comap e := by
              ext x y
              simp [SimpleGraph.compl_adj]
            have hle : ((G.comap e)ᶜ).map e ≤ Gᶜ := by
              rw [hEq]
              exact SimpleGraph.map_comap_le e Gᶜ
            exact hm.mono hle
          refine Or.inr ⟨u, ?_⟩
          rw [SimpleGraph.isNClique_iff]
          constructor
          · exact hucl
          · simpa [u] using hs.2
      · have hT : B ≤ T.card := by
          have hScard : S.card < A := Nat.lt_of_not_ge hS
          have hVAB : V.card = A + B - 1 := by rw [hV, hAB]
          rw [hVAB] at hST
          omega
        obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hT
        let e : Fin B ↪ Fin (Nat.choose (k + l - 2) (k - 1)) := (U.orderEmbOfFin hUcard).toEmbedding
        let H : SimpleGraph (Fin B) := G.comap e
        rcases hrecB H with h | h
        · rcases h with ⟨s, hs⟩
          rw [SimpleGraph.isNClique_iff] at hs
          let u := s.map e
          have hucl : G.IsClique u := by
            have hm := hs.1.finsetMap (f := e)
            exact hm.mono (SimpleGraph.map_comap_le e G)
          refine Or.inl ⟨u, ?_⟩
          rw [SimpleGraph.isNClique_iff]
          constructor
          · exact hucl
          · simpa [u] using hs.2
        · rcases h with ⟨s, hs⟩
          rw [SimpleGraph.isNClique_iff] at hs
          let u := s.map e
          have hucl : Gᶜ.IsClique u := by
            have hm := hs.1.finsetMap (f := e)
            have hEq : (G.comap e)ᶜ = Gᶜ.comap e := by
              ext x y
              simp [SimpleGraph.compl_adj]
            have hle : ((G.comap e)ᶜ).map e ≤ Gᶜ := by
              rw [hEq]
              exact SimpleGraph.map_comap_le e Gᶜ
            exact hm.mono hle
          have hucard : u.card = l - 1 := by simp [u, hs.2]
          have huT : ∀ x ∈ u, x ∈ T := by
            intro x hx
            rcases Finset.mem_map.mp hx with ⟨y, hy, rfl⟩
            have hyU : e y ∈ U := by simpa [e] using Finset.orderEmbOfFin_mem U hUcard y
            exact hUT hyU
          have huv : v ∉ u := by
            intro hvu
            have hvT : v ∈ T := huT v hvu
            have hvV : v ∈ V := (Finset.mem_filter.mp hvT).1
            simpa [V] using hvV
          refine Or.inr ⟨insert v u, ?_⟩
          rw [SimpleGraph.isNClique_iff]
          constructor
          · rw [SimpleGraph.isClique_iff]
            intro x hx y hy hxy
            rcases Finset.mem_insert.mp hx with rfl | hx
            · rcases Finset.mem_insert.mp hy with rfl | hy
              · exact (hxy rfl).elim
              · have hnot : ¬ G.Adj v y := (Finset.mem_filter.mp (huT y hy)).2
                exact (G.compl_adj v y).mpr ⟨hxy, hnot⟩
            · rcases Finset.mem_insert.mp hy with rfl | hy
              · have hnot : ¬ G.Adj v x := (Finset.mem_filter.mp (huT x hx)).2
                exact (G.compl_adj x v).mpr ⟨hxy, fun h => hnot h.symm⟩
              · exact hucl hx hy hxy
          · rw [Finset.card_insert_of_notMem huv, hucard]
            omega
  exact hmain (k + l) k l rfl hk hl
