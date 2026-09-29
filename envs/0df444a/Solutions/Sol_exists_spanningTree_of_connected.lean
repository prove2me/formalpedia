-- Prove2me | solution 1 for exists_spanningTree_of_connected
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/0f2b8989-238b-5a29-83bb-799f440c2281

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_spanningTree_of_connected

set_option autoImplicit false

open Finset

namespace SpanningTreeGrowth

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def bdry (hd tl : E → V) (c : E → ℤ) (w : V) : ℤ :=
  (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e)

omit [Fintype V] [DecidableEq E] in
theorem bdry_add (hd tl : E → V) (c d : E → ℤ) (w : V) :
    bdry hd tl (c + d) w = bdry hd tl c w + bdry hd tl d w := by
  simp only [bdry, Pi.add_apply, sum_add_distrib]; ring

omit [Fintype V] [DecidableEq E] in
theorem bdry_sub (hd tl : E → V) (c d : E → ℤ) (w : V) :
    bdry hd tl (c - d) w = bdry hd tl c w - bdry hd tl d w := by
  simp only [bdry, Pi.sub_apply, sum_sub_distrib]; ring

omit [Fintype V] [DecidableEq E] in
theorem bdry_neg (hd tl : E → V) (c : E → ℤ) (w : V) :
    bdry hd tl (-c) w = -bdry hd tl c w := by
  simp only [bdry, Pi.neg_apply, sum_neg_distrib]; ring

omit [Fintype V] in
theorem bdry_single (hd tl : E → V) (e : E) (w : V) :
    bdry hd tl (Pi.single e 1) w = (if w = hd e then 1 else 0) - (if w = tl e then 1 else 0) := by
  simp only [bdry]
  rw [sum_pi_single', sum_pi_single']
  simp only [mem_filter, mem_univ, true_and]
  have e1 : (hd e = w) = (w = hd e) := propext eq_comm
  have e2 : (tl e = w) = (w = tl e) := propext eq_comm
  simp only [e1, e2]

omit [Fintype V] [DecidableEq E] in

theorem sum_bdry_eq (hd tl : E → V) (c : E → ℤ) (A : Finset V) :
    (∑ w ∈ A, bdry hd tl c w) =
      (∑ e with hd e ∈ A, c e) - (∑ e with tl e ∈ A, c e) := by
  simp only [bdry, sum_sub_distrib]
  congr 1
  · rw [← sum_fiberwise_of_maps_to (s := univ.filter fun e => hd e ∈ A) (t := A) (g := hd)
      (fun e he => (mem_filter.1 he).2)]
    refine sum_congr rfl fun w hw => sum_congr ?_ fun _ _ => rfl
    ext e; simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hw, h⟩, fun h => h.2⟩
  · rw [← sum_fiberwise_of_maps_to (s := univ.filter fun e => tl e ∈ A) (t := A) (g := tl)
      (fun e he => (mem_filter.1 he).2)]
    refine sum_congr rfl fun w hw => sum_congr ?_ fun _ _ => rfl
    ext e; simp only [mem_filter, mem_univ, true_and]
    exact ⟨fun h => ⟨h ▸ hw, h⟩, fun h => h.2⟩

def grown (root : V) (vs : ℕ → V) (i : ℕ) : Finset V :=
  insert root ((range i).image vs)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem mem_grown {root : V} {vs : ℕ → V} {i : ℕ} {v : V} :
    v ∈ grown root vs i ↔ v = root ∨ ∃ i' < i, vs i' = v := by
  simp [grown]

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem root_mem_grown (root : V) (vs : ℕ → V) (i : ℕ) : root ∈ grown root vs i :=
  mem_insert_self _ _

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem grown_mono (root : V) (vs : ℕ → V) {i i' : ℕ} (h : i ≤ i') :
    grown root vs i ⊆ grown root vs i' := by
  intro v hv
  rw [mem_grown] at hv ⊢
  rcases hv with rfl | ⟨k, hk, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k, lt_of_lt_of_le hk h, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem apply_mem_grown_succ (root : V) (vs : ℕ → V) (i : ℕ) :
    vs i ∈ grown root vs (i + 1) :=
  mem_grown.2 (Or.inr ⟨i, Nat.lt_succ_self i, rfl⟩)

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem grown_succ (root : V) (vs : ℕ → V) (i : ℕ) :
    grown root vs (i + 1) = insert (vs i) (grown root vs i) := by
  ext v
  simp only [mem_grown, mem_insert]
  constructor
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact Or.inr (Or.inl rfl)
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact Or.inr (Or.inr ⟨k, hk, rfl⟩)
      · exact Or.inl rfl
  · rintro (rfl | rfl | ⟨k, hk, rfl⟩)
    · exact Or.inr ⟨i, Nat.lt_succ_self i, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨k, Nat.lt_succ_of_lt hk, rfl⟩

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem grown_congr (root : V) {vs vs' : ℕ → V} {i : ℕ} (h : ∀ i' < i, vs' i' = vs i') :
    grown root vs' i = grown root vs i := by
  ext v
  simp only [mem_grown]
  constructor
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨k, hk, (h k hk).symm⟩
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨k, hk, h k hk⟩

def Good (hd tl : E → V) (root : V) (vs : ℕ → V) (es : ℕ → E) (k : ℕ) : Prop :=
  ∀ i < k, vs i ∉ grown root vs i ∧
    ((hd (es i) = vs i ∧ tl (es i) ∈ grown root vs i) ∨
      (tl (es i) = vs i ∧ hd (es i) ∈ grown root vs i))

omit [Fintype V] [Fintype E] [DecidableEq E] in
theorem card_grown {hd tl : E → V} {root : V} {vs : ℕ → V} {es : ℕ → E}
    {k : ℕ} (hG : Good hd tl root vs es k) : ∀ i ≤ k, (grown root vs i).card = i + 1 := by
  intro i
  induction i with
  | zero => intro _; simp [grown]
  | succ i ih =>
    intro hi
    rw [grown_succ, card_insert_of_notMem (hG i hi).1, ih (Nat.le_of_succ_le hi)]

end SpanningTreeGrowth

open SpanningTreeGrowth

theorem solution {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
    (hd tl : E → V)
    (hconn : ∀ u v : V, ∃ c : E → ℤ,
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0)) :
    ∃ T : Finset E, ∀ u v : V, ∃! c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, (∑ e with hd e = w, c e) - (∑ e with tl e = w, c e) =
        (if w = v then 1 else 0) - (if w = u then 1 else 0) := by
  classical

  rcases isEmpty_or_nonempty V with hV | hV
  · exact ⟨∅, fun u => hV.elim u⟩

  rcases isEmpty_or_nonempty E with hE | hE
  · refine ⟨∅, fun u v => ⟨0, ⟨fun e _ => rfl, fun w => ?_⟩, fun c _ => funext fun e => hE.elim e⟩⟩
    obtain ⟨c, hc⟩ := hconn u v
    have := hc w
    have h0 : ∀ (p : E → Prop) [DecidablePred p], (∑ e with p e, c e) = 0 :=
      fun p _ => sum_eq_zero fun e _ => hE.elim e
    rw [h0, h0] at this
    simp only [Pi.zero_apply, sum_const_zero]
    exact this
  set root : V := Classical.arbitrary V
  set n : ℕ := Fintype.card V - 1 with hn
  have hn1 : n + 1 = Fintype.card V := by
    have : 0 < Fintype.card V := Fintype.card_pos
    omega

  have hcross : ∀ A : Finset V, root ∈ A → A ≠ univ →
      ∃ e, (hd e ∉ A ∧ tl e ∈ A) ∨ (tl e ∉ A ∧ hd e ∈ A) := by
    intro A hr hA
    obtain ⟨v, hv⟩ : ∃ v, v ∉ A := by
      by_contra h; push Not at h
      exact hA (eq_univ_of_forall h)
    obtain ⟨c, hc⟩ := hconn root v
    by_contra hno
    have hiff : ∀ e, hd e ∈ A ↔ tl e ∈ A := by
      intro e
      by_cases h1 : hd e ∈ A <;> by_cases h2 : tl e ∈ A
      · exact iff_of_true h1 h2
      · exact absurd ⟨e, Or.inr ⟨h2, h1⟩⟩ hno
      · exact absurd ⟨e, Or.inl ⟨h1, h2⟩⟩ hno
      · exact iff_of_false h1 h2
    have hsum : (∑ w ∈ A, bdry hd tl c w) = 0 := by
      rw [sum_bdry_eq]
      have : (univ.filter fun e => hd e ∈ A) = univ.filter fun e => tl e ∈ A := by
        ext e; simp [hiff e]
      rw [this, sub_self]
    have hsum' : (∑ w ∈ A, bdry hd tl c w) = -1 := by
      have : ∀ w ∈ A, bdry hd tl c w = (if w = v then 1 else 0) - (if w = root then 1 else 0) :=
        fun w _ => hc w
      rw [sum_congr rfl this, sum_sub_distrib, sum_ite_eq', sum_ite_eq', if_neg hv, if_pos hr]
      rfl
    omega

  have hgrow : ∀ k, k + 1 ≤ Fintype.card V →
      ∃ (vs : ℕ → V) (es : ℕ → E), Good hd tl root vs es k := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨fun _ => root, fun _ => Classical.arbitrary E, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    | succ k ih =>
      intro hk
      obtain ⟨vs, es, hG⟩ := ih (by omega)
      have hAcard : (grown root vs k).card = k + 1 := card_grown hG k le_rfl
      have hAnu : grown root vs k ≠ univ := by
        intro h; rw [h, card_univ] at hAcard; omega
      obtain ⟨e, he⟩ := hcross _ (root_mem_grown _ _ _) hAnu
      obtain ⟨vn, hvn, hside⟩ : ∃ vn : V, vn ∉ grown root vs k ∧
          ((hd e = vn ∧ tl e ∈ grown root vs k) ∨ (tl e = vn ∧ hd e ∈ grown root vs k)) := by
        rcases he with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨hd e, h1, Or.inl ⟨rfl, h2⟩⟩
        · exact ⟨tl e, h1, Or.inr ⟨rfl, h2⟩⟩
      refine ⟨Function.update vs k vn, Function.update es k e, ?_⟩
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · have hvi : Function.update vs k vn i = vs i := Function.update_of_ne (ne_of_lt hi) _ _
        have hei : Function.update es k e i = es i := Function.update_of_ne (ne_of_lt hi) _ _
        have hgr : grown root (Function.update vs k vn) i = grown root vs i :=
          grown_congr root fun i' hi' => Function.update_of_ne (by omega) _ _
        rw [hvi, hei, hgr]
        exact hG i hi
      · have hvi : Function.update vs i vn i = vn := Function.update_self _ _ _
        have hei : Function.update es i e i = e := Function.update_self _ _ _
        have hgr : grown root (Function.update vs i vn) i = grown root vs i :=
          grown_congr root fun i' hi' => Function.update_of_ne (by omega) _ _
        rw [hvi, hei, hgr]
        exact ⟨hvn, hside⟩
  obtain ⟨vs, es, hG⟩ := hgrow n (by omega)

  have huniv : grown root vs n = univ := by
    apply eq_univ_of_card
    rw [card_grown hG n le_rfl, hn1]
  have hends : ∀ i < n, hd (es i) ∈ grown root vs (i + 1) ∧ tl (es i) ∈ grown root vs (i + 1) := by
    intro i hi
    rcases (hG i hi).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨h1 ▸ apply_mem_grown_succ root vs i, grown_mono root vs (Nat.le_succ i) h2⟩
    · exact ⟨grown_mono root vs (Nat.le_succ i) h2, h1 ▸ apply_mem_grown_succ root vs i⟩
  set T : Finset E := (range n).image es with hT
  have hesT : ∀ i < n, es i ∈ T := fun i hi => mem_image.2 ⟨i, mem_range.2 hi, rfl⟩

  have hreach : ∀ i ≤ n, ∀ v ∈ grown root vs i, ∃ c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, bdry hd tl c w = (if w = v then 1 else 0) - (if w = root then 1 else 0) := by
    intro i
    induction i with
    | zero =>
      intro _ v hv
      have hv' : v = root := by simpa [grown] using hv
      subst hv'
      exact ⟨0, fun _ _ => rfl, fun w => by simp [bdry]⟩
    | succ i ih =>
      intro hi v hv
      rw [grown_succ, mem_insert] at hv
      rcases hv with rfl | hv
      · have hi' : i < n := hi
        rcases (hG i hi').2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · obtain ⟨c, hcT, hcb⟩ := ih (Nat.le_of_succ_le hi) _ h2
          refine ⟨c + Pi.single (es i) 1, fun e he => ?_, fun w => ?_⟩
          · have hne : e ≠ es i := fun h => he (h ▸ hesT i hi')
            simp [hcT e he, Pi.single_eq_of_ne hne]
          · rw [bdry_add, hcb, bdry_single, h1]
            ring
        · obtain ⟨c, hcT, hcb⟩ := ih (Nat.le_of_succ_le hi) _ h2
          refine ⟨c - Pi.single (es i) 1, fun e he => ?_, fun w => ?_⟩
          · have hne : e ≠ es i := fun h => he (h ▸ hesT i hi')
            simp [hcT e he, Pi.single_eq_of_ne hne]
          · rw [bdry_sub, hcb, bdry_single, h1]
            ring
      · exact ih (Nat.le_of_succ_le hi) v hv
  have hreach' : ∀ v, ∃ c : E → ℤ, (∀ e ∉ T, c e = 0) ∧
      ∀ w, bdry hd tl c w = (if w = v then 1 else 0) - (if w = root then 1 else 0) :=
    fun v => hreach n le_rfl v (huniv ▸ mem_univ v)

  have hzero : ∀ z : E → ℤ, (∀ e ∉ T, z e = 0) → (∀ w, bdry hd tl z w = 0) → z = 0 := by
    intro z hzT hzb

    have helim : ∀ r, ∀ i < n, n ≤ i + r → z (es i) = 0 := by
      intro r
      induction r with
      | zero => intro i hi h; omega
      | succ r ih =>
        intro i hi hir
        by_cases h : n ≤ i + r
        · exact ih i hi h
        · have hnot := (hG i hi).1

          have hvan : ∀ e, e ≠ es i → (hd e = vs i ∨ tl e = vs i) → z e = 0 := by
            intro e hne hend
            by_cases heT : e ∈ T
            · rw [hT, mem_image] at heT
              obtain ⟨i', hi', rfl⟩ := heT
              rw [mem_range] at hi'
              rcases lt_trichotomy i' i with hlt | rfl | hgt
              · exfalso
                obtain ⟨h1, h2⟩ := hends i' hi'
                rcases hend with h3 | h3
                · exact hnot (h3 ▸ grown_mono root vs (by omega) h1)
                · exact hnot (h3 ▸ grown_mono root vs (by omega) h2)
              · exact absurd rfl hne
              · exact ih i' hi' (by omega)
            · exact hzT e heT
          have hb := hzb (vs i)
          simp only [bdry, sum_filter] at hb
          rw [sum_eq_single (es i) (fun e _ hne => ?_) (fun h => absurd (mem_univ _) h),
            sum_eq_single (es i) (fun e _ hne => ?_) (fun h => absurd (mem_univ _) h)] at hb
          · rcases (hG i hi).2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · have h3 : tl (es i) ≠ vs i := fun h => hnot (h ▸ h2)
              rw [if_pos h1, if_neg h3, sub_zero] at hb
              exact hb
            · have h3 : hd (es i) ≠ vs i := fun h => hnot (h ▸ h2)
              rw [if_neg h3, if_pos h1, zero_sub, neg_eq_zero] at hb
              exact hb
          · by_cases h1 : tl e = vs i
            · rw [if_pos h1]; exact hvan e hne (Or.inr h1)
            · rw [if_neg h1]
          · by_cases h1 : hd e = vs i
            · rw [if_pos h1]; exact hvan e hne (Or.inl h1)
            · rw [if_neg h1]
    funext e
    by_cases heT : e ∈ T
    · rw [hT, mem_image] at heT
      obtain ⟨i, hi, rfl⟩ := heT
      exact helim n i (mem_range.1 hi) (by omega)
    · exact hzT e heT

  refine ⟨T, fun u v => ?_⟩
  obtain ⟨cu, hcuT, hcub⟩ := hreach' u
  obtain ⟨cv, hcvT, hcvb⟩ := hreach' v
  refine ⟨cv - cu, ⟨fun e he => by simp [hcuT e he, hcvT e he], fun w => ?_⟩, ?_⟩
  · have := bdry_sub hd tl cv cu w
    simp only [bdry] at this
    rw [this]
    change bdry hd tl cv w - bdry hd tl cu w = _
    rw [hcvb, hcub]
    ring
  · rintro c ⟨hcT, hcb⟩
    have h := hzero (c - (cv - cu)) (fun e he => by simp [hcT e he, hcuT e he, hcvT e he])
      (fun w => by
        rw [bdry_sub, bdry_sub, hcvb, hcub]
        change ((∑ e with hd e = w, c e) - ∑ e with tl e = w, c e) - _ = 0
        rw [hcb w]
        ring)
    exact sub_eq_zero.1 h

end S_exists_spanningTree_of_connected
end P2MW
export P2MW.S_exists_spanningTree_of_connected (solution)
