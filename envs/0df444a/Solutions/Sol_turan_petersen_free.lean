-- Prove2me | solution 1 for turan_petersen_free
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:23:37.474399+00:00
-- url     : https://prove2.me/submissions/94800d3a-d8ed-4648-9863-afc693722220

import Mathlib

set_option autoImplicit false

open SimpleGraph Filter
open scoped Topology

namespace PetersenBound

def edges : Finset (Nat × Nat) :=
  {(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)}

def graph : SimpleGraph (Fin 10) where
  Adj i j := (i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

instance : DecidableRel graph.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ edges ∨ (j.val, i.val) ∈ edges))

def color : Fin 10 → Fin 3 := ![0,1,0,1,2,1,2,2,0,0]

theorem color_proper : ∀ i j : Fin 10, graph.Adj i j → color i ≠ color j := by
  decide

theorem contained_tripartite : graph ⊑ completeEquipartiteGraph 3 10 := by
  refine ⟨{
    toHom := {
      toFun := fun i => (color i, i)
      map_rel' := ?_ }
    injective' := ?_ }⟩
  · intro i j hij
    exact color_proper i j hij
  · intro i j hij
    exact congrArg Prod.snd hij

theorem exists_degree_threshold :
    ∃ N : Nat, ∀ n : Nat, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      graph.Free G → (G.minDegree : ℝ) < (5 / 8 : ℝ) * n := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (eventually_completeEquipartiteGraph_isContained_of_minDegree (by norm_num : (0 : ℝ) < 1 / 8) 2 10)
  refine ⟨N, fun n hn G _ hfree => ?_⟩
  by_contra! hdeg
  apply hfree
  apply contained_tripartite.trans
  apply hN n hn
  norm_num at *
  exact hdeg

theorem extremal_bound (N : Nat)
    (hN : ∀ n : Nat, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      graph.Free G → (G.minDegree : ℝ) < (5 / 8 : ℝ) * n) :
    ∀ n : Nat, (extremalNumber n graph : ℝ) ≤ (5 / 16 : ℝ) * n * (n + 1) + (N : ℝ)^2 := by
  intro n
  induction n with
  | zero =>
      rw [← Fintype.card_fin 0, extremalNumber_le_iff_of_nonneg graph (by positivity)]
      intro G _ _
      have h := G.card_edgeFinset_le_card_choose_two
      simp only [Fintype.card_fin, Nat.choose_zero_succ] at h
      have hz : G.edgeFinset.card = 0 := Nat.eq_zero_of_le_zero h
      simp [hz]
  | succ n ih =>
      rw [← Fintype.card_fin (n + 1), extremalNumber_le_iff_of_nonneg graph (by positivity)]
      intro G _ hfree
      simp only [Fintype.card_fin]
      by_cases hn : N ≤ n + 1
      · obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
        have hdeg := hN (n + 1) hn G hfree
        rw [hv] at hdeg
        have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
        rw [card_edgeFinset_deleteIncidenceSet] at hdel
        simp only [Fintype.card_fin, Nat.add_sub_cancel] at hdel
        have hle := G.degree_le_card_edgeFinset v
        have hdelR' : (G.edgeFinset.card : ℝ) - G.degree v ≤ (extremalNumber n graph : ℝ) := by
          simpa only [Nat.cast_sub hle] using (show ((G.edgeFinset.card - G.degree v : Nat) : ℝ) ≤
            (extremalNumber n graph : ℝ) from by exact_mod_cast hdel)
        push_cast at *
        nlinarith
      · have hsize : (n + 1 : ℝ) ≤ N := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hn))
        have hedge := G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ 2)
        simp only [Fintype.card_fin] at hedge
        have hedgeR : (G.edgeFinset.card : ℝ) ≤ (n + 1 : ℝ)^2 := by
          exact_mod_cast hedge
        push_cast
        nlinarith [sq_nonneg ((N : ℝ) - (n + 1)), (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
          (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem eventually_edge_bound :
    ∃ M : Nat, ∀ n : Nat, M ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      graph.Free G → (G.edgeFinset.card : ℝ) ≤ (3 / 8 : ℝ) * n * (n - 1) := by
  obtain ⟨N, hN⟩ := exists_degree_threshold
  refine ⟨64 * (N^2 + 1), fun n hn G _ hfree => ?_⟩
  have hb := extremal_bound N hN n
  have he : (G.edgeFinset.card : ℝ) ≤ (extremalNumber n graph : ℝ) := by
    exact_mod_cast (show G.edgeFinset.card ≤ extremalNumber n graph from by
      simpa using card_edgeFinset_le_extremalNumber hfree)
  have hnR : 64 * ((N : ℝ)^2 + 1) ≤ n := by exact_mod_cast hn
  have hn64 : (64 : ℝ) ≤ n := by nlinarith [sq_nonneg (N : ℝ)]
  have hnquad : 64 * (n : ℝ) ≤ (n : ℝ)^2 := by nlinarith
  nlinarith [sq_nonneg (N : ℝ)]

end PetersenBound

theorem solution :
    ∀ eps : ℝ, 0 < eps →
    ∃ N : ℕ, ∀ (n : ℕ) (_ : N ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let petersen_edges : Finset (ℕ × ℕ) :=
        {(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
          (5,7),(7,9),(9,6),(6,8),(8,5)}
      (¬∃ (phi : Fin 10 → Fin n), Function.Injective phi ∧
        ∀ i j : Fin 10, (i.val, j.val) ∈ petersen_edges → G.Adj (phi i) (phi j)) →
      (G.edgeFinset.card : ℝ) ≤ (3/4 + eps) * n * (n - 1) / 2 := by
  intro eps heps
  obtain ⟨N, hN⟩ := PetersenBound.eventually_edge_bound
  refine ⟨max N 1, fun n hn G _ hfree => ?_⟩
  have hnN := (le_max_left N 1).trans hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast ((le_max_right N 1).trans hn)
  have hgraph : PetersenBound.graph.Free G := by
    rintro ⟨f⟩
    apply hfree
    refine ⟨f, f.injective, fun i j hij => ?_⟩
    exact f.toHom.map_rel (Or.inl hij)
  have hb := hN n hnN G hgraph
  have hprod : 0 ≤ eps * (n : ℝ) * (n - 1) := by positivity
  nlinarith

#print axioms solution
