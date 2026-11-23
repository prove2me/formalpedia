-- Prove2me | solution 1 for proposition_4_5_safe_of_visible
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:56:55.093771+00:00
-- url     : https://prove2.me/submissions/6ca342e3-e231-41b4-b50a-f07d11180daf

import Definitions.Def_DistributedMWC440_UpperBound_Operations

open scoped ENNReal
open MeasureTheory ProbabilityTheory
open DistributedMWC440.UpperBound
noncomputable section

private lemma p45_walkWeight_nil {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (u : V) :
    walkWeight W (SimpleGraph.Walk.nil : W.graph.Walk u u) = 0 := by
  simp [walkWeight, OAI.PlanarL1.walkLength]

private lemma p45_walkWeight_cons {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) {a b c : V} (h : W.graph.Adj a b)
    (P : W.graph.Walk b c) :
    walkWeight W (P.cons h) = W.length a b + walkWeight W P := by
  simp [walkWeight, OAI.PlanarL1.walkLength]

private lemma p45_walkWeight_append {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) {a b c : V} (P : W.graph.Walk a b) (Q : W.graph.Walk b c) :
    walkWeight W (P.append Q) = walkWeight W P + walkWeight W Q := by
  induction P with
  | nil => simp [walkWeight, OAI.PlanarL1.walkLength]
  | cons h P ih => simp_all [p45_walkWeight_cons, add_assoc]

private lemma p45_walkWeight_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) {a b : V} (P : W.graph.Walk a b) :
    0 ≤ walkWeight W P := by
  induction P with
  | nil => simp [p45_walkWeight_nil]
  | cons h P ih =>
    rw [p45_walkWeight_cons]
    exact add_nonneg (W.nonnegative _ _ h) ih

private lemma p45_dist_le_walk {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) {a b : V} (P : W.graph.Walk a b) :
    dist W a b ≤ walkWeight W P := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨Q, rfl⟩; exact p45_walkWeight_nonneg W Q⟩
  · exact ⟨P, rfl⟩

private lemma p45_dist_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected) (a b : V) :
    0 ≤ dist W a b := by
  apply le_csInf
  · obtain ⟨Q⟩ := hW a b
    exact ⟨walkWeight W Q, Q, rfl⟩
  · rintro _ ⟨Q, rfl⟩
    exact p45_walkWeight_nonneg W Q

private lemma p45_dist_le_add_walk {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected) (x y z : V) (Q : W.graph.Walk y z) :
    dist W x z ≤ dist W x y + walkWeight W Q := by
  refine le_of_forall_pos_le_add ?_
  intro eta heta
  obtain ⟨P⟩ := hW x y
  let A : Set ℝ := {a | ∃ P : W.graph.Walk x y, walkWeight W P = a}
  have hne : A.Nonempty := ⟨walkWeight W P, P, rfl⟩
  have hbdd : BddBelow A :=
    ⟨0, by rintro _ ⟨T, rfl⟩; exact p45_walkWeight_nonneg W T⟩
  have hlt : sInf A < dist W x y + eta := by
    change dist W x y < dist W x y + eta
    exact lt_add_of_pos_right _ heta
  obtain ⟨a, ⟨T, rfl⟩, ha⟩ := (csInf_lt_iff hbdd hne).mp hlt
  have hcat := p45_dist_le_walk W (T.append Q)
  rw [p45_walkWeight_append] at hcat
  linarith

private lemma p45_setDist_le_dist {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected) (R : Finset V) (x r : V) (hr : r ∈ R) :
    setDist W x R ≤ dist W x r := by
  apply csInf_le
  · exact ⟨0, by rintro _ ⟨t, ht, rfl⟩; exact p45_dist_nonneg W hW x t⟩
  · exact ⟨r, hr, rfl⟩

private lemma p45_support_subset {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b c d : V}
    (P : G.Walk a b) (hP : ¬P.Nil) (Q : G.Walk c d)
    (h : ∀ e ∈ P.edges, e ∈ Q.edges) : P.support ⊆ Q.support := by
  induction P with
  | nil => simp at hP
  | @cons u v w hab P ih =>
    intro z hz
    rw [SimpleGraph.Walk.support_cons] at hz
    simp only [List.mem_cons] at hz
    have he : s(u,v) ∈ (P.cons hab).edges := by simp
    rcases hz with rfl | hz
    · exact Q.fst_mem_support_of_mem_edges (h _ he)
    · by_cases hnil : P.Nil
      · have hvw : v = w := hnil.eq
        subst w
        have hzv : z = v := by simpa [hnil.eq_nil] using hz
        subst z
        exact Q.snd_mem_support_of_mem_edges (h _ he)
      · exact ih hnil (fun e heP => h _ (by simp [heP])) hz

theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (W : WGraph V) (hW : W.graph.Connected)
    (S R : Finset V) (k d ε : ℝ) (δ : Shifts S) (s : S)
    (hcapture : Captures W S R k d δ s) (q : V) (hq : q ∈ R)
    (hqr : dist W s.val q = setDist W s.val R)
    {C : Cycle W} {a b : V} (P : W.graph.Walk a b)
    (hseg : IsSegment C R P)
    (hvis : Visible C q P (d-2*ε*deltaMax S k d))
    {v : V} (hv : v ∈ P.support) : Safe W S k d ε δ s v := by
  intro s' hs'
  obtain ⟨r, hr, Q, hQpath, hQcycle, hcontain, hQweight⟩ := hvis
  have hrR : r ∈ R := by rcases hr with rfl | rfl <;> simp_all [IsSegment]
  have hnil : ¬P.Nil := fun h => hseg.2.2.1 h.eq
  have hvQ : v ∈ Q.support := p45_support_subset P hnil Q hcontain hv
  have hsplit : walkWeight W (Q.takeUntil v hvQ) + walkWeight W (Q.dropUntil v hvQ) =
      walkWeight W Q := by
    rw [← p45_walkWeight_append W (Q.takeUntil v hvQ) (Q.dropUntil v hvQ), Q.take_spec]
  have hsv : dist W s.val v ≤ dist W s.val q + walkWeight W (Q.takeUntil v hvQ) :=
    p45_dist_le_add_walk W hW _ _ _ _
  have hs'r : dist W s'.val r ≤ dist W s'.val v + walkWeight W (Q.dropUntil v hvQ) :=
    p45_dist_le_add_walk W hW _ _ _ _
  have hsetr : setDist W s'.val R ≤ dist W s'.val r :=
    p45_setDist_le_dist W hW R s'.val r hrR
  have hcap := hcapture s' hs'
  dsimp [Safe] at *
  linarith