-- Prove2me | solution 1 for erdos_gallai_path_conjecture
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:52:34.940346+00:00
-- url     : https://prove2.me/submissions/a04728d8-7d5a-4006-944c-f209294a61a3

import Mathlib

open Function Set Finset

namespace ErdosGallai

variable {V : Type*} (G : SimpleGraph V)

def PathSeq {n : ℕ} (p : Fin (n + 1) → V) : Prop :=
  Injective p ∧ ∀ i : Fin n, G.Adj (p i.castSucc) (p i.succ)

theorem PathSeq.reverse {n : ℕ} {p : Fin (n + 1) → V} (hp : PathSeq G p) :
    PathSeq G (fun i => p i.rev) := by
  refine ⟨hp.1.comp Fin.rev_injective, ?_⟩
  intro i
  simpa only [Fin.rev_castSucc, Fin.rev_succ] using (hp.2 i.rev).symm

theorem PathSeq.prepend {n : ℕ} {p : Fin (n + 1) → V} (hp : PathSeq G p)
    {x : V} (hx : x ∉ Set.range p) (hxp : G.Adj x (p 0)) :
    PathSeq G (Fin.cons x p) := by
  constructor
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _; rfl
      · intro hij
        exact False.elim (hx ⟨j, (by simpa only [Fin.cons_zero, Fin.cons_succ] using hij : x = p j).symm⟩)
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact False.elim (hx ⟨i, (by simpa only [Fin.cons_zero, Fin.cons_succ] using hij : p i = x)⟩)
      · intro hij
        exact congrArg Fin.succ (hp.1 (by simpa only [Fin.cons_succ] using hij))
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using hxp
    · change G.Adj (p j.castSucc) (p j.succ)
      exact hp.2 j

/-- Reverse the suffix after `j`; the order becomes `0,...,j,n,...,j+1`. -/
def turnIndex {n : ℕ} (j : Fin n) (i : Fin (n + 1)) : Fin (n + 1) :=
  ⟨if i.val ≤ j.val then i.val else n + j.val + 1 - i.val, by
    split_ifs <;> omega⟩

theorem turnIndex_involutive {n : ℕ} (j : Fin n) : Involutive (turnIndex j) := by
  intro i
  apply Fin.ext
  simp only [turnIndex]
  split_ifs <;> omega

theorem turnIndex_injective {n : ℕ} (j : Fin n) : Injective (turnIndex j) :=
  (turnIndex_involutive j).injective

@[simp] theorem turnIndex_zero {n : ℕ} (j : Fin n) : turnIndex j 0 = 0 := by
  apply Fin.ext
  simp [turnIndex]

@[simp] theorem turnIndex_last {n : ℕ} (j : Fin n) :
    turnIndex j (Fin.last n) = j.succ := by
  apply Fin.ext
  simp only [turnIndex, Fin.val_last, Fin.val_succ]
  split_ifs <;> omega

theorem pathSeq_turn {n : ℕ} {p : Fin (n + 1) → V} (hp : PathSeq G p)
    (j : Fin n) (hj : G.Adj (p j.castSucc) (p (Fin.last n))) :
    PathSeq G (fun i => p (turnIndex j i)) := by
  refine ⟨hp.1.comp (turnIndex_injective j), ?_⟩
  intro i
  by_cases hij : i.val < j.val
  · have h₁ : turnIndex j i.castSucc = i.castSucc := by
      apply Fin.ext
      simp only [turnIndex, Fin.val_castSucc]
      split_ifs <;> omega
    have h₂ : turnIndex j i.succ = i.succ := by
      apply Fin.ext
      simp only [turnIndex, Fin.val_succ]
      split_ifs <;> omega
    simpa only [h₁, h₂] using hp.2 i
  · by_cases heq : i.val = j.val
    · have h₁ : turnIndex j i.castSucc = j.castSucc := by
        apply Fin.ext
        simp only [turnIndex, Fin.val_castSucc]
        split_ifs <;> omega
      have h₂ : turnIndex j i.succ = Fin.last n := by
        apply Fin.ext
        simp only [turnIndex, Fin.val_succ, Fin.val_last]
        split_ifs <;> omega
      simpa only [h₁, h₂] using hj
    · let a : Fin n := ⟨n + j.val - i.val, by omega⟩
      have h₁ : turnIndex j i.castSucc = a.succ := by
        apply Fin.ext
        simp only [turnIndex, Fin.val_castSucc, Fin.val_succ, a]
        split_ifs <;> omega
      have h₂ : turnIndex j i.succ = a.castSucc := by
        apply Fin.ext
        simp only [turnIndex, Fin.val_succ, Fin.val_castSucc, a]
        split_ifs <;> omega
      simpa only [h₁, h₂] using (hp.2 a).symm

theorem pathSeq_rotate {n : ℕ} {p : Fin (n + 1) → V} (hp : PathSeq G p)
    (hc : G.Adj (p (Fin.last n)) (p 0)) (a : Fin (n + 1)) :
    PathSeq G (fun i => p (i + a)) := by
  have hstep (i : Fin n) : finRotate (n + 1) i.castSucc = i.succ := by
    exact finRotate_of_lt i.isLt
  have hcyc (i : Fin (n + 1)) : G.Adj (p i) (p (finRotate (n + 1) i)) := by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [finRotate_last] using hc
    · simpa only [hstep] using hp.2 j
  refine ⟨hp.1.comp (fun _ _ h => add_right_cancel h), ?_⟩
  intro i
  have h := hcyc (i.castSucc + a)
  have heq : finRotate (n + 1) (i.castSucc + a) = i.succ + a := by
    rw [finRotate_apply, ← hstep, finRotate_apply]
    abel
  simpa only [heq] using h

theorem neighbor_range_of_maximal {n : ℕ} {p : Fin (n + 1) → V} (hp : PathSeq G p)
    (hmax : ∀ m : ℕ, ∀ q : Fin (m + 1) → V, PathSeq G q → m ≤ n)
    {x : V} (hx : G.Adj x (p 0)) : x ∈ Set.range p := by
  by_contra h
  have := hmax (n + 1) (Fin.cons x p) (hp.prepend G h hx)
  omega

theorem closed_path_spans_of_maximal [Fintype V] {n : ℕ} {p : Fin (n + 1) → V}
    (hconn : G.Connected) (hp : PathSeq G p)
    (hc : G.Adj (p (Fin.last n)) (p 0))
    (hmax : ∀ m : ℕ, ∀ q : Fin (m + 1) → V, PathSeq G q → m ≤ n) :
    Surjective p := by
  have hclosed {x y : V} (hx : x ∈ Set.range p) (hxy : G.Adj x y) :
      y ∈ Set.range p := by
    obtain ⟨a, rfl⟩ := hx
    have hy := neighbor_range_of_maximal G (pathSeq_rotate G hp hc a) hmax
      (by simpa only [zero_add] using hxy.symm)
    obtain ⟨i, hi⟩ := hy
    exact ⟨i + a, hi⟩
  have hwalk {x y : V} (w : G.Walk x y) : x ∈ Set.range p → y ∈ Set.range p := by
    induction w with
    | nil => exact id
    | cons h w ih => exact fun hx => ih (hclosed hx h)
  intro y
  obtain ⟨w⟩ := hconn.preconnected (p 0) y
  exact hwalk w ⟨0, rfl⟩

theorem endpoint_neighbor_counts [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {n : ℕ} {p : Fin (n + 1) → V} (hp : PathSeq G p)
    (hmax : ∀ m : ℕ, ∀ q : Fin (m + 1) → V, PathSeq G q → m ≤ n) :
    (Finset.univ.filter (fun i : Fin n => G.Adj (p 0) (p i.succ))).card = G.degree (p 0) ∧
    (Finset.univ.filter (fun i : Fin n => G.Adj (p i.castSucc) (p (Fin.last n)))).card =
      G.degree (p (Fin.last n)) := by
  constructor
  · change _ = (G.neighborFinset (p 0)).card
    apply Finset.card_bij (fun i _ => p i.succ)
    · intro i hi
      simpa only [SimpleGraph.mem_neighborFinset, Finset.mem_filter, Finset.mem_univ, true_and]
        using hi
    · intro i _ j _ hij
      exact Fin.succ_injective n (hp.1 hij)
    · intro x hx
      have hxadj : G.Adj (p 0) x := by simpa only [SimpleGraph.mem_neighborFinset] using hx
      obtain ⟨j, hj⟩ := neighbor_range_of_maximal G hp hmax hxadj.symm
      have hj0 : 0 < j.val := by
        by_contra h
        have hjz : j = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
        subst j
        exact hxadj.ne hj
      let i : Fin n := ⟨j.val - 1, by omega⟩
      have hij : i.succ = j := Fin.ext (by dsimp [i]; omega)
      refine ⟨i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hij, hj]
        exact hxadj
      · simpa only [hij] using hj
  · change _ = (G.neighborFinset (p (Fin.last n))).card
    apply Finset.card_bij (fun i _ => p i.castSucc)
    · intro i hi
      have h : G.Adj (p i.castSucc) (p (Fin.last n)) := by simpa using hi
      simpa only [SimpleGraph.mem_neighborFinset] using h.symm
    · intro i _ j _ hij
      exact Fin.castSucc_injective n (hp.1 hij)
    · intro x hx
      have hxadj : G.Adj (p (Fin.last n)) x := by
        simpa only [SimpleGraph.mem_neighborFinset] using hx
      have hxrange := neighbor_range_of_maximal G (hp.reverse G) hmax
        (by simpa only [Fin.rev_zero] using hxadj.symm)
      obtain ⟨j', hj'⟩ := hxrange
      let j := j'.rev
      have hj : p j = x := hj'
      have hjn : j.val < n := by
        by_contra h
        have hjlast : j = Fin.last n := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [hjlast] at hj
        exact hxadj.ne hj
      let i : Fin n := ⟨j.val, hjn⟩
      have hij : i.castSucc = j := Fin.ext rfl
      refine ⟨i, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and, hij, hj]
        exact hxadj.symm
      · simpa only [hij] using hj

theorem exists_long_path_of_min_degree [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (k : ℕ) (hconn : G.Connected) (hcard : k + 1 < Fintype.card V)
    (hdeg : ∀ v, k < 2 * G.degree v) :
    ∃ p : Fin (k + 2) → V, Injective p ∧
      ∀ i : Fin (k + 1), G.Adj (p i.castSucc) (p i.succ) := by
  classical
  let lengths : Set ℕ := {m | ∃ p : Fin (m + 1) → V, PathSeq G p}
  have hfinite : lengths.Finite := (Set.finite_le_nat (Fintype.card V)).subset (by
    rintro m ⟨p, hp⟩
    have h := Fintype.card_le_of_injective p hp.1
    simp only [Fintype.card_fin] at h
    exact (show m ≤ Fintype.card V by omega))
  obtain ⟨v⟩ := hconn.nonempty
  have hzero : 0 ∈ lengths := by
    refine ⟨fun _ => v, ?_, ?_⟩
    · intro i j _
      apply Fin.ext
      omega
    · exact fun i => Fin.elim0 i
  obtain ⟨n, hn, hnmax⟩ := hfinite.exists_maximal ⟨0, hzero⟩
  obtain ⟨p, hp⟩ := hn
  have hmax (m : ℕ) (q : Fin (m + 1) → V) (hq : PathSeq G q) : m ≤ n := by
    have h := hnmax (show m ∈ lengths from ⟨q, hq⟩)
    omega
  by_cases hlong : k + 1 ≤ n
  · refine ⟨fun i => p ⟨i.val, by omega⟩, ?_, ?_⟩
    · intro i j hij
      exact Fin.ext (Fin.mk.inj (hp.1 hij))
    · intro i
      exact hp.2 ⟨i.val, by omega⟩
  · have hnle : n ≤ k := by omega
    let A := Finset.univ.filter (fun i : Fin n => G.Adj (p 0) (p i.succ))
    let B := Finset.univ.filter (fun i : Fin n => G.Adj (p i.castSucc) (p (Fin.last n)))
    have hcounts := endpoint_neighbor_counts G hp hmax
    have hsum : n < A.card + B.card := by
      change n < (Finset.univ.filter _).card + (Finset.univ.filter _).card
      rw [hcounts.1, hcounts.2]
      have h₁ := hdeg (p 0)
      have h₂ := hdeg (p (Fin.last n))
      omega
    have hnd : ¬Disjoint A B := by
      intro hdisj
      have hle := Finset.card_le_card (Finset.subset_univ (A ∪ B))
      rw [Finset.card_union_of_disjoint hdisj, Finset.card_univ, Fintype.card_fin] at hle
      omega
    obtain ⟨j, hja, hjb⟩ := Finset.not_disjoint_iff.mp hnd
    have hj₁ : G.Adj (p 0) (p j.succ) := by simpa [A] using hja
    have hj₂ : G.Adj (p j.castSucc) (p (Fin.last n)) := by simpa [B] using hjb
    have hq := pathSeq_turn G hp j hj₂
    have hqclose : G.Adj (p (turnIndex j (Fin.last n))) (p (turnIndex j 0)) := by
      simpa only [turnIndex_last, turnIndex_zero] using hj₁.symm
    have hsurj := closed_path_spans_of_maximal G hconn hq hqclose hmax
    have hle := Fintype.card_le_of_surjective _ hsurj
    simp only [Fintype.card_fin] at hle
    omega

end ErdosGallai

namespace ErdosGallai

universe u

theorem degree_le_of_component_path_bound {k : ℕ}
    (hpath : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      H.Connected → k + 1 < Fintype.card W → (∀ w, k < 2 * H.degree w) →
      ∃ p : Fin (k + 2) → W, Function.Injective p ∧
        ∀ i : Fin (k + 1), H.Adj (p i.castSucc) (p i.succ))
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hmin : ∀ v, k < 2 * G.degree v)
    (hno : ¬∃ p : Fin (k + 2) → V, Function.Injective p ∧
      ∀ i : Fin (k + 1), G.Adj (p i.castSucc) (p i.succ)) :
    ∀ v, G.degree v ≤ k := by
  classical
  intro v
  by_contra hv
  let C := G.connectedComponentMk v
  letI : Fintype C := Fintype.ofFinite C
  have hdegree (w : C) : C.toSimpleGraph.degree w = G.degree w := by
    rw [← SimpleGraph.card_neighborSet_eq_degree, ← SimpleGraph.card_neighborSet_eq_degree]
    apply Fintype.card_congr
    exact {
      toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, C.mem_supp_of_adj_mem_supp w.property x.property⟩, x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : k + 1 < Fintype.card C := by
    have h := C.toSimpleGraph.degree_lt_card_verts (⟨v, rfl⟩ : C)
    rw [hdegree] at h
    change G.degree v < Fintype.card C at h
    omega
  obtain ⟨p, hp, hpa⟩ := hpath C.toSimpleGraph C.connected_toSimpleGraph hcard
    (fun w => by rw [hdegree]; exact hmin w)
  exact hno ⟨fun i => (p i).val, Subtype.val_injective.comp hp, hpa⟩

end ErdosGallai

open Finset
open scoped BigOperators

namespace ErdosGallai

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def localDegree (s : Finset V) (v : V) : ℕ := (s.filter (G.Adj v)).card

def localDegreeSum (s : Finset V) : ℕ := ∑ v ∈ s, localDegree G s v

theorem localDegree_erase (s : Finset V) (v w : V) (hv : v ∈ s) :
    localDegree G s w = localDegree G (s.erase v) w + if G.Adj w v then 1 else 0 := by
  unfold localDegree
  rw [filter_erase]
  by_cases h : G.Adj w v
  · rw [if_pos h]
    exact (card_erase_add_one (mem_filter.mpr ⟨hv, h⟩)).symm
  · simp [h]

theorem localDegreeSum_erase (s : Finset V) (v : V) (hv : v ∈ s) :
    localDegreeSum G s = localDegreeSum G (s.erase v) + 2 * localDegree G s v := by
  have hrow : (∑ w ∈ s.erase v, if G.Adj w v then 1 else 0) = localDegree G s v := by
    simp_rw [G.adj_comm, ← sum_filter]
    simp only [sum_const, smul_eq_mul, mul_one]
    rw [filter_erase, erase_eq_of_notMem]
    · rfl
    · simp
  unfold localDegreeSum
  rw [← add_sum_erase s (localDegree G s) hv]
  conv_lhs => arg 2; arg 2; ext w; rw [localDegree_erase G s v w hv]
  rw [sum_add_distrib, hrow]
  omega

theorem degree_induce_finset (s : Finset V) (v : s) :
    (G.induce (s : Set V)).degree v = localDegree G s v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  unfold localDegree
  apply card_bij (fun x _ => x.val)
  · intro x hx
    exact mem_filter.mpr ⟨x.property, (mem_filter.mp hx).2⟩
  · intro x hx y hy hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, (mem_filter.mp hx).1⟩, ?_, rfl⟩
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hx).2⟩

theorem localDegree_univ [Fintype V] (v : V) :
    localDegree G univ v = G.degree v := by
  rw [localDegree, ← SimpleGraph.neighborFinset_eq_filter,
    SimpleGraph.card_neighborFinset_eq_degree]

theorem localDegreeSum_univ [Fintype V] :
    localDegreeSum G univ = 2 * G.edgeFinset.card := by
  simp only [localDegreeSum, localDegree_univ]
  exact G.sum_degrees_eq_twice_card_edges

theorem localDegreeSum_le (s : Finset V) (k : ℕ)
    (h : ∀ v ∈ s, localDegree G s v ≤ k) : localDegreeSum G s ≤ k * s.card := by
  calc
    localDegreeSum G s ≤ ∑ _v ∈ s, k := sum_le_sum h
    _ = k * s.card := by simp [mul_comm]

end ErdosGallai

open Finset

namespace ErdosGallai

universe u

theorem edge_bound_of_connected_path_bound {k : ℕ}
    (hpath : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W) [DecidableRel H.Adj],
      H.Connected → k + 1 < Fintype.card W → (∀ w, k < 2 * H.degree w) →
      ∃ p : Fin (k + 2) → W, Function.Injective p ∧
        ∀ i : Fin (k + 1), H.Adj (p i.castSucc) (p i.succ))
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hno : ¬∃ p : Fin (k + 2) → V, Function.Injective p ∧
      ∀ i : Fin (k + 1), G.Adj (p i.castSucc) (p i.succ)) :
    2 * G.edgeFinset.card ≤ k * Fintype.card V := by
  classical
  have bound (s : Finset V) : localDegreeSum G s ≤ k * s.card := by
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      by_cases hsmall : ∃ v ∈ s, 2 * localDegree G s v ≤ k
      · obtain ⟨v, hv, hdegree⟩ := hsmall
        have hrec := ih (s.erase v) (erase_ssubset hv)
        have hsum := localDegreeSum_erase G s v hv
        have hcard := card_erase_add_one hv
        nlinarith
      · have hmin (v : s) : k < 2 * (G.induce (s : Set V)).degree v := by
          rw [degree_induce_finset]
          exact lt_of_not_ge fun h => hsmall ⟨v.val, v.property, h⟩
        have hsub : ¬∃ p : Fin (k + 2) → s, Function.Injective p ∧
            ∀ i : Fin (k + 1), (G.induce (s : Set V)).Adj (p i.castSucc) (p i.succ) := by
          rintro ⟨p, hp, ha⟩
          exact hno ⟨fun i => (p i).val, Subtype.val_injective.comp hp, ha⟩
        have hdegrees := degree_le_of_component_path_bound hpath
          (G.induce (s : Set V)) hmin hsub
        apply localDegreeSum_le
        intro v hv
        simpa only [degree_induce_finset] using hdegrees ⟨v, hv⟩
  simpa only [localDegreeSum_univ, card_univ] using bound univ

end ErdosGallai

theorem solution (n k : ℕ) (hk : 1 ≤ k) :
    ∀ G : SimpleGraph (Fin n), [DecidableRel G.Adj] →
      (¬∃ path : Fin (k + 2) → Fin n, Function.Injective path ∧
        ∀ i : Fin (k + 1), G.Adj (path i.castSucc) (path i.succ)) →
      2 * G.edgeFinset.card ≤ k * n := by
  intro G inst hno
  have bound := ErdosGallai.edge_bound_of_connected_path_bound
    (fun {_} _ _ H _ hconn hcard hdeg =>
      ErdosGallai.exists_long_path_of_min_degree H k hconn hcard hdeg) G hno
  simpa only [Fintype.card_fin] using bound

#check @solution
#print axioms solution
