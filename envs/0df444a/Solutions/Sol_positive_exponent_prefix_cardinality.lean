-- Prove2me | solution 1 for positive_exponent_prefix_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-09T04:18:26.037619+00:00
-- url     : https://prove2.me/submissions/9045314f-2db0-4746-a5ad-4001f29a5c3a

/-
  Counting positive exponent prefixes.

  The finite cut set is not used as a substitute for the exponent tuples: the
  first part below gives an explicit composition map from the bounded tuples to
  positive compositions, and the second part identifies fixed-length
  compositions with their interior cuts.
-/

import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false

open scoped BigOperators

def PositiveExponentPrefix (k n' : ℕ) :=
  {a : Fin k → Fin n' // (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'}

def PositiveCompositionPrefix (k n' : ℕ) :=
  {c : Composition n' // c.length = k + 1}

instance positiveExponentPrefixFintype (k n' : ℕ) : Fintype (PositiveExponentPrefix k n') :=
  by
    classical
    unfold PositiveExponentPrefix
    infer_instance

instance positiveCompositionPrefixFintype (k n' : ℕ) : Fintype (PositiveCompositionPrefix k n') :=
  by
    classical
    unfold PositiveCompositionPrefix
    infer_instance

def tupleBlocks {k n' : ℕ} (a : PositiveExponentPrefix k n') : List ℕ :=
  List.ofFn (fun i : Fin k => (a.1 i).val) ++ [n' - ∑ i, (a.1 i).val]

private lemma tupleBlocks_length {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    (tupleBlocks a).length = k + 1 := by
  simp [tupleBlocks]

private lemma tupleBlocks_sum {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    (tupleBlocks a).sum = n' := by
  have hle : (∑ i, (a.1 i).val) ≤ n' := Nat.le_of_lt a.2.2
  simp only [tupleBlocks, List.sum_append, List.sum_singleton, List.sum_ofFn]
  exact Nat.add_sub_of_le hle

private lemma tupleBlocks_pos {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    ∀ {x}, x ∈ tupleBlocks a → 0 < x := by
  intro x hx
  simp only [tupleBlocks, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    exact a.2.1 i
  · have hlt := a.2.2
    omega

def tupleToComposition {k n' : ℕ} (a : PositiveExponentPrefix k n') : Composition n' :=
  { blocks := tupleBlocks a
    blocks_pos := tupleBlocks_pos a
    blocks_sum := tupleBlocks_sum a }

private lemma tupleToComposition_length {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    (tupleToComposition a).length = k + 1 := by
  exact tupleBlocks_length a

private lemma tupleToComposition_block {k n' : ℕ} (a : PositiveExponentPrefix k n')
    (i : Fin k) :
    (tupleToComposition a).blocksFun ⟨i.1, by rw [tupleToComposition_length a]; omega⟩ =
      (a.1 i).val := by
  simp [tupleToComposition, tupleBlocks, Composition.blocksFun]

private lemma composition_index {k n' : ℕ} (c : PositiveCompositionPrefix k n')
    (i : Fin k) : i.1 < c.1.length := by
  rw [c.2]
  exact Nat.lt_succ_of_lt i.isLt

private lemma composition_positive {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    0 < n' := by
  have i0 : Fin c.1.length := ⟨0, by rw [c.2]; omega⟩
  have hsum := c.1.sum_blocksFun
  have hblock := c.1.one_le_blocksFun i0
  have hle : c.1.blocksFun i0 ≤ ∑ i : Fin c.1.length, c.1.blocksFun i :=
    Finset.single_le_sum (f := c.1.blocksFun) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i0)
  omega

private def compositionTuple {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
  Fin k → Fin n' := fun i =>
  ⟨c.1.blocksFun ⟨i.1, composition_index c i⟩, by
    have hne : c.1 ≠ Composition.single n' (composition_positive c) := by
      intro h
      have hlen := c.2
      have hi := i.isLt
      rw [h, Composition.single_length] at hlen
      omega
    have hlt := (Composition.ne_single_iff (composition_positive c)).mp hne
      ⟨i.1, composition_index c i⟩
    omega⟩

private lemma compositionTuple_pos {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    ∀ i, 0 < (compositionTuple c i).val := by
  intro i
  exact lt_of_lt_of_le Nat.zero_lt_one (c.1.one_le_blocksFun ⟨i.1, composition_index c i⟩)

private lemma compositionTuple_sum_lt {k n' : ℕ} (_hn' : 0 < n')
    (c : PositiveCompositionPrefix k n') :
    (∑ i, (compositionTuple c i).val) < n' := by
  have hklen : k < c.1.length := by rw [c.2]; omega
  have hsum : (∑ i, (compositionTuple c i).val) = c.1.sizeUpTo k := by
    let g : Fin k → ℕ := fun i => c.1.blocksFun ⟨i.1, composition_index c i⟩
    have hlist : List.ofFn g = c.1.blocks.take k := by
      apply List.ext_getElem
      · simp [hklen.le]
      · intro i hi₁ hi₂
        simp [g, Composition.blocksFun]
    calc
      (∑ i, (compositionTuple c i).val) = (List.ofFn g).sum := by
        simp [g, compositionTuple, List.sum_ofFn]
      _ = (c.1.blocks.take k).sum := by rw [hlist]
      _ = c.1.sizeUpTo k := rfl
  rw [hsum]
  have hstrict := c.1.sizeUpTo_strict_mono hklen
  have hfull : c.1.sizeUpTo (k + 1) = n' := by
    simpa [c.2] using c.1.sizeUpTo_length
  omega

private def compositionToTuple {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    PositiveExponentPrefix k n' :=
  ⟨compositionTuple c, compositionTuple_pos c, compositionTuple_sum_lt (composition_positive c) c⟩

private lemma tupleToCompositionToTuple {k n' : ℕ} (a : PositiveExponentPrefix k n') :
    compositionToTuple ⟨tupleToComposition a, tupleToComposition_length a⟩ = a := by
  apply Subtype.ext
  funext i
  simp [compositionToTuple, compositionTuple, tupleToComposition_block]

private lemma compositionToTupleToComposition {k n' : ℕ} (c : PositiveCompositionPrefix k n') :
    tupleToComposition (compositionToTuple c) = c.1 := by
  apply Composition.ext
  apply List.ext_getElem
  · change (tupleToComposition (compositionToTuple c)).length = c.1.length
    calc
      (tupleToComposition (compositionToTuple c)).length = k + 1 :=
        tupleToComposition_length (compositionToTuple c)
      _ = c.1.length := c.2.symm
  · intro i hi₁ hi₂
    by_cases hki : i < k
    · let j : Fin k := ⟨i, hki⟩
      have hb := tupleToComposition_block (compositionToTuple c) j
      simpa [tupleBlocks, compositionToTuple, compositionTuple, Composition.blocksFun,
        hki, hi₁, hi₂, j] using hb
    · have hi₁' : i < k + 1 := by
        change i < (tupleToComposition (compositionToTuple c)).length at hi₁
        rw [tupleToComposition_length (compositionToTuple c)] at hi₁
        exact hi₁
      have hik : i = k := by omega
      subst i
      have hklen : k < c.1.length := by rw [c.2]; omega
      have hsum : ∑ i, ((compositionToTuple c).1 i).val = c.1.sizeUpTo k := by
        let g : Fin k → ℕ := fun i => c.1.blocksFun ⟨i.1, composition_index c i⟩
        have hlist : List.ofFn g = c.1.blocks.take k := by
          apply List.ext_getElem
          · simp [hklen.le]
          · intro j hj₁ hj₂
            simp [g, Composition.blocksFun]
        calc
          (∑ i, ((compositionToTuple c).1 i).val) = (List.ofFn g).sum := by
            simp [g, compositionToTuple, compositionTuple, List.sum_ofFn]
          _ = (c.1.blocks.take k).sum := by rw [hlist]
          _ = c.1.sizeUpTo k := rfl
      have hsize := c.1.sizeUpTo_succ hklen
      have hfull : c.1.sizeUpTo (k + 1) = n' := by
        simpa [c.2] using c.1.sizeUpTo_length
      rw [hfull] at hsize
      have hlast : c.1.blocks[k] = n' - ∑ i, ((compositionToTuple c).1 i).val := by
        omega
      calc
        (tupleToComposition (compositionToTuple c)).blocks[k] =
            n' - ∑ i, ((compositionToTuple c).1 i).val := by
              simp [tupleToComposition, tupleBlocks, List.getElem_append_right,
                List.length_ofFn]
        _ = c.1.blocks[k] := hlast.symm

private def tupleCompositionEquiv (k n' : ℕ) :
    PositiveExponentPrefix k n' ≃ PositiveCompositionPrefix k n' :=
  { toFun := fun a => ⟨tupleToComposition a, tupleToComposition_length a⟩
    invFun := compositionToTuple
    left_inv := tupleToCompositionToTuple
    right_inv := fun c => Subtype.ext (compositionToTupleToComposition c) }

private def InteriorCuts (k n' : ℕ) :=
  {s : Finset (Fin (n' - 1)) // s.card = k}

instance interiorCutsFintype (k n' : ℕ) : Fintype (InteriorCuts k n') := by
  classical
  unfold InteriorCuts
  infer_instance

private lemma inverse_composition_length {n' : ℕ} (hn' : 0 < n')
    (s : Finset (Fin (n' - 1))) :
    ((compositionAsSetEquiv n').symm s).length = s.card + 1 := by
  let sh : Fin (n' - 1) → Fin n'.succ := fun j => ⟨j.val + 1, by omega⟩
  have hsh : Function.Injective sh := by
    intro x y h
    apply Fin.ext
    have h' := congrArg Fin.val h
    dsimp [sh] at h'
    omega
  have himage : (s.image sh).card = s.card := by
    exact Finset.card_image_iff.mpr (Set.injOn_of_injective hsh)
  have h0 : (0 : Fin n'.succ) ∉ s.image sh := by
    simp only [Finset.mem_image]
    rintro ⟨j, hj, h⟩
    have h' := congrArg Fin.val h
    dsimp [sh] at h'
    omega
  have hlast : Fin.last n' ∉ s.image sh := by
    simp only [Finset.mem_image]
    rintro ⟨j, hj, h⟩
    have h' := congrArg Fin.val h
    dsimp [sh] at h'
    omega
  have h01 : (0 : Fin n'.succ) ≠ Fin.last n' := by
    intro h
    have h' := congrArg Fin.val h
    exact hn'.ne' h'.symm
  have hbound : ((compositionAsSetEquiv n').symm s).boundaries =
      insert 0 (insert (Fin.last n') (s.image sh)) := by
    dsimp [compositionAsSetEquiv]
    ext i
    simp only [Set.mem_toFinset, Finset.mem_insert, Finset.mem_image]
    constructor
    · rintro (rfl | rfl | ⟨j, hj, h⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨j, hj, by apply Fin.ext; dsimp [sh]; exact h.symm⟩)
    · rintro (rfl | rfl | ⟨j, hj, rfl⟩)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ⟨j, hj, rfl⟩)
  rw [CompositionAsSet.length, hbound]
  have h0' : (0 : Fin n'.succ) ∉ insert (Fin.last n') (s.image sh) := by
    simp [h01, h0]
  rw [Finset.card_insert_of_notMem h0', Finset.card_insert_of_notMem hlast, himage]
  omega

private lemma composition_cut_card {n' : ℕ} (hn' : 0 < n')
    (c : Composition n') :
    (compositionAsSetEquiv n' c.toCompositionAsSet).card = c.length - 1 := by
  let s := compositionAsSetEquiv n' c.toCompositionAsSet
  have h := inverse_composition_length hn' s
  have hleft : ((compositionAsSetEquiv n').symm s).length = c.length := by
    rw [show (compositionAsSetEquiv n').symm s = c.toCompositionAsSet by
      simp [s]]
    exact c.toCompositionAsSet_length
  have hs : s.card + 1 = c.length := by omega
  have hc : c.length = s.card + 1 := hleft.symm.trans h
  symm
  exact (Nat.sub_eq_iff_eq_add (by omega)).mpr hc

private def compositionCutsEquiv (k n' : ℕ) (hn' : 0 < n') :
    PositiveCompositionPrefix k n' ≃ InteriorCuts k n' := by
  let e : PositiveCompositionPrefix k n' → InteriorCuts k n' := fun c =>
    ⟨compositionAsSetEquiv n' c.1.toCompositionAsSet, by
      have h := composition_cut_card hn' c.1
      have hc := c.2
      omega⟩
  let f : InteriorCuts k n' → PositiveCompositionPrefix k n' := fun s =>
    ⟨((compositionAsSetEquiv n').symm s.1).toComposition, by
      have h := inverse_composition_length hn' s.1
      have hlen := CompositionAsSet.toComposition_length ((compositionAsSetEquiv n').symm s.1)
      have hs := s.2
      omega⟩
  exact
    { toFun := e
      invFun := f
      left_inv := by
        intro c
        apply Subtype.ext
        change ((compositionAsSetEquiv n').symm
          (compositionAsSetEquiv n' c.1.toCompositionAsSet)).toComposition = c.1
        rw [(compositionAsSetEquiv n').symm_apply_apply]
        exact (compositionEquiv n').left_inv c.1
      right_inv := by
        intro s
        apply Subtype.ext
        dsimp [e, f]
        change compositionAsSetEquiv n'
          (((compositionAsSetEquiv n').symm s.1).toComposition.toCompositionAsSet) = s.1
        rw [show ((compositionAsSetEquiv n').symm s.1).toComposition.toCompositionAsSet =
            ((compositionAsSetEquiv n').symm s.1) from
          (compositionEquiv n').right_inv ((compositionAsSetEquiv n').symm s.1)]
        exact (compositionAsSetEquiv n').apply_symm_apply s.1 }

theorem solution (k n' : ℕ) (hn' : 0 < n') :
    Fintype.card {a : Fin k → Fin n' //
      (∀ i, 0 < (a i).val) ∧ (∑ i, (a i).val) < n'} = Nat.choose (n' - 1) k := by
  change Fintype.card (PositiveExponentPrefix k n') = Nat.choose (n' - 1) k
  rw [Fintype.card_congr (tupleCompositionEquiv k n'),
    Fintype.card_congr (compositionCutsEquiv k n' hn')]
  simp [InteriorCuts]

#print axioms solution
