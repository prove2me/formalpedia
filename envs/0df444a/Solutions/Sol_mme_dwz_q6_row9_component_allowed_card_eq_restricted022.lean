-- Prove2me | solution 1 for mme_dwz_q6_row9_component_allowed_card_eq_restricted022
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T07:48:59.042546+00:00
-- url     : https://prove2.me/submissions/1321f4e1-34e9-44d5-bf29-e4d599266dab

import Mathlib.Tactic
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_central_restricted_word_projectors
import Definitions.Def_mme_dwz_table2_component_022_word_data
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_cw_square_restricted_central_power_words

open MME MME.DWZFineChannel MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

namespace MME.DWZCentral022RestrictedBridge

theorem fine022SourcePair_grade_two
    (c : Fine022Channel 6) :
    cwSquarePairGrade 6 (fine022SourcePair 6 c 2) = 2 := by
  rcases c with c | c
  · fin_cases c
    decide
  · rcases c with ij | c
    · rcases ij with ⟨i, j⟩
      have hiT : i.val + 1 ≠ 7 := by omega
      have hjT : j.val + 1 ≠ 7 := by omega
      simp [fine022SourcePair, cwSquarePairGrade, cwSquareCoordGrade,
        cwM, hiT, hjT]
    · fin_cases c
      decide

def fine022CoarsePair (c : Fine022Channel 6) : CoarsePair 6 2 :=
  ⟨fine022SourcePair 6 c 2, fine022SourcePair_grade_two c⟩

def coarsePairFine022 (p : CoarsePair 6 2) : Fine022Channel 6 :=
  if p.1.1.val = 7 then
    Sum.inl 0
  else if p.1.1.val = 0 then
    Sum.inr (Sum.inr 0)
  else
    Sum.inr (Sum.inl
      (Fin.ofNat 6 (p.1.1.val - 1), Fin.ofNat 6 (p.1.2.val - 1)))

theorem coarsePairFine022_left_inverse :
    Function.LeftInverse coarsePairFine022 fine022CoarsePair := by
  intro c
  rcases c with c | c
  · fin_cases c
    rfl
  · rcases c with ij | c
    · rcases ij with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> rfl
    · fin_cases c
      rfl

theorem coarsePairFine022_right_inverse :
    Function.RightInverse coarsePairFine022 fine022CoarsePair := by
  rintro ⟨⟨a, b⟩, hp⟩
  apply Subtype.ext
  fin_cases a <;> fin_cases b <;>
    simp [coarsePairFine022, fine022CoarsePair, fine022SourcePair,
      cwSquarePairGrade, cwSquareCoordGrade, cwO, cwM, cwT] at hp ⊢

noncomputable def fine022CoarseEquiv :
    Fine022Channel 6 ≃ CoarsePair 6 2 where
  toFun := fine022CoarsePair
  invFun := coarsePairFine022
  left_inv := coarsePairFine022_left_inverse
  right_inv := coarsePairFine022_right_inverse

theorem fine022CoarseEquiv_val (c : Fine022Channel 6) :
    (fine022CoarseEquiv c).1 = fine022SourcePair 6 c 2 := rfl

end MME.DWZCentral022RestrictedBridge

open MME.DWZCentral022RestrictedBridge

namespace MME.DWZCentral022AllowedExtraction

abbrev row9Length (m : ℕ) : ℕ :=
  MME.DWZTable2Counts.component 9 * m

def row9Allowed (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m)) : Prop :=
  componentWordAllowed 9 m w

def row9AllowedWord (m : ℕ) :=
  {w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m) //
    row9Allowed m w}

noncomputable instance row9AllowedWordFintype (m : ℕ) :
    Fintype (row9AllowedWord.{u} m) := by
  unfold row9AllowedWord
  letI : DecidablePred (row9Allowed m) := Classical.decPred _
  infer_instance

noncomputable def row9DecodedWord (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m)) :
    Fin (row9Length m) → Fine022Channel 6 := fun r ↦
  fine022CoarseEquiv.symm (PowIndex.get (row9Length m) w r).down

end MME.DWZCentral022AllowedExtraction

open MME.DWZCentral022AllowedExtraction


namespace MME.DWZCentral022AllowedCard

def fine022Class : Fine022Channel 6 → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

def reverseOuterClass : Fin 3 → Fin 3 := ![2, 1, 0]

def fine022MiddleLabel : Fine022Channel 6 → Fin 6 × Fin 6
  | Sum.inr (Sum.inl ij) => ij
  | _ => (0, 0)

theorem fine022Coarse_leftGrade
    (c : Fine022Channel 6) :
    (fine022CoarseEquiv c).leftGrade =
      reverseOuterClass (fine022Class c) := by
  rcases c with c | c
  · fin_cases c
    rfl
  · rcases c with ij | c
    · rcases ij with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> rfl
    · fin_cases c
      rfl

theorem row9DecodedWord_leftGrade (m : ℕ)
    (w : PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m))
    (r : Fin (row9Length m)) :
    (PowIndex.get (row9Length m) w r).leftGrade =
      reverseOuterClass (fine022Class (row9DecodedWord m w r)) := by
  change (PowIndex.get (row9Length m) w r).down.leftGrade = _
  let c := fine022CoarseEquiv.symm
    (PowIndex.get (row9Length m) w r).down
  have h : fine022CoarseEquiv c =
      (PowIndex.get (row9Length m) w r).down :=
    fine022CoarseEquiv.apply_symm_apply _
  calc
    (PowIndex.get (row9Length m) w r).down.leftGrade =
        (fine022CoarseEquiv c).leftGrade :=
      congrArg CoarsePair.leftGrade h.symm
    _ = reverseOuterClass (fine022Class c) := fine022Coarse_leftGrade c

abbrev row9OuterCount (m : ℕ) : ℕ :=
  MME.DWZTable2Counts.split 9 0 * m

abbrev row9MiddleCount (m : ℕ) : ℕ :=
  MME.DWZTable2Counts.split 9 1 * m

noncomputable def row9ToCentralWord (m : ℕ)
    (w : row9AllowedWord.{u} m) :
    CentralRestricted022Word 6 (row9Length m)
      (row9OuterCount m) (row9MiddleCount m) := by
  let p : Fin (row9Length m) → Fin 3 := fun r ↦
    fine022Class (row9DecodedWord m w.1 r)
  have hp : ∀ c,
      Fintype.card {r : Fin (row9Length m) // p r = c} =
        centralSplitMultiplicity (row9OuterCount m)
          (row9MiddleCount m) c := by
    intro c
    fin_cases c
    · have hallowed := w.2 (2 : Fin 3)
      change Fintype.card {r : Fin (row9Length m) //
          p r = (0 : Fin 3)} = row9OuterCount m
      have htypes :
          {r : Fin (row9Length m) // p r = (0 : Fin 3)} =
            {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (2 : Fin 3)} := by
        congr 1
        funext r
        apply propext
        rw [row9DecodedWord_leftGrade]
        rcases h : row9DecodedWord m w.1 r with c | c
        · fin_cases c
          simp [p, fine022Class, reverseOuterClass, h]
        · rcases c with ij | c
          · simp [p, fine022Class, reverseOuterClass, h]
          · fin_cases c
            simp [p, fine022Class, reverseOuterClass, h]
      calc
        Fintype.card {r : Fin (row9Length m) // p r = (0 : Fin 3)} =
            Nat.card {r : Fin (row9Length m) // p r = (0 : Fin 3)} :=
          Nat.card_eq_fintype_card.symm
        _ = Nat.card {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (2 : Fin 3)} := congrArg Nat.card htypes
        _ = Fintype.card {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (2 : Fin 3)} := Nat.card_eq_fintype_card
        _ = row9OuterCount m := by
          exact hallowed
    · have hallowed := w.2 (1 : Fin 3)
      change Fintype.card {r : Fin (row9Length m) //
          p r = (1 : Fin 3)} = row9MiddleCount m
      have htypes :
          {r : Fin (row9Length m) // p r = (1 : Fin 3)} =
            {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (1 : Fin 3)} := by
        congr 1
        funext r
        apply propext
        rw [row9DecodedWord_leftGrade]
        rcases h : row9DecodedWord m w.1 r with c | c
        · fin_cases c
          simp [p, fine022Class, reverseOuterClass, h]
        · rcases c with ij | c
          · simp [p, fine022Class, reverseOuterClass, h]
          · fin_cases c
            simp [p, fine022Class, reverseOuterClass, h]
      calc
        Fintype.card {r : Fin (row9Length m) // p r = (1 : Fin 3)} =
            Nat.card {r : Fin (row9Length m) // p r = (1 : Fin 3)} :=
          Nat.card_eq_fintype_card.symm
        _ = Nat.card {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (1 : Fin 3)} := congrArg Nat.card htypes
        _ = Fintype.card {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (1 : Fin 3)} := Nat.card_eq_fintype_card
        _ = row9MiddleCount m := by
          exact hallowed
    · have hallowed := w.2 (0 : Fin 3)
      change Fintype.card {r : Fin (row9Length m) //
          p r = (2 : Fin 3)} = row9OuterCount m
      have htypes :
          {r : Fin (row9Length m) // p r = (2 : Fin 3)} =
            {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (0 : Fin 3)} := by
        congr 1
        funext r
        apply propext
        rw [row9DecodedWord_leftGrade]
        rcases h : row9DecodedWord m w.1 r with c | c
        · fin_cases c
          simp [p, fine022Class, reverseOuterClass, h]
        · rcases c with ij | c
          · simp [p, fine022Class, reverseOuterClass, h]
          · fin_cases c
            simp [p, fine022Class, reverseOuterClass, h]
      calc
        Fintype.card {r : Fin (row9Length m) // p r = (2 : Fin 3)} =
            Nat.card {r : Fin (row9Length m) // p r = (2 : Fin 3)} :=
          Nat.card_eq_fintype_card.symm
        _ = Nat.card {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (0 : Fin 3)} := congrArg Nat.card htypes
        _ = Fintype.card {r : Fin (row9Length m) //
              (PowIndex.get (row9Length m) w.1 r).leftGrade =
                (0 : Fin 3)} := Nat.card_eq_fintype_card
        _ = row9OuterCount m := by
          exact hallowed
  let pattern : CentralSplitPattern (row9Length m)
      (row9OuterCount m) (row9MiddleCount m) := ⟨p, hp⟩
  exact ⟨pattern, fun r ↦
    fine022MiddleLabel (row9DecodedWord m w.1 r.1)⟩

theorem encode_row9ToCentralWord (m : ℕ)
    (w : row9AllowedWord.{u} m) :
    encodeCentralRestricted022Word (row9ToCentralWord m w) =
      row9DecodedWord m w.1 := by
  funext r
  rcases h : row9DecodedWord m w.1 r with c | c
  · fin_cases c
    simp [row9ToCentralWord, fine022Class, fine022MiddleLabel, h,
      encodeCentralRestricted022Word]
    rfl
  · rcases c with ij | c
    · simp [row9ToCentralWord, fine022Class, fine022MiddleLabel, h,
        encodeCentralRestricted022Word]
      rfl
    · fin_cases c
      simp [row9ToCentralWord, fine022Class, fine022MiddleLabel, h,
        encodeCentralRestricted022Word]
      rfl

theorem row9ToCentralWord_injective (m : ℕ) :
    Function.Injective (row9ToCentralWord.{u} m) := by
  intro w v h
  apply Subtype.ext
  apply (PowIndex.equivFun (LiftedCoarsePair.{u} 6 2)
    (row9Length m)).injective
  funext r
  apply ULift.ext
  apply fine022CoarseEquiv.symm.injective
  have hencoded := congrArg encodeCentralRestricted022Word h
  rw [encode_row9ToCentralWord, encode_row9ToCentralWord] at hencoded
  exact congrFun hencoded r

noncomputable def centralWordToRow9Pow (m : ℕ)
    (w : CentralRestricted022Word 6 (row9Length m)
      (row9OuterCount m) (row9MiddleCount m)) :
    PowIndex (LiftedCoarsePair.{u} 6 2) (row9Length m) :=
  PowIndex.ofFun (row9Length m) (fun r ↦
    ULift.up (fine022CoarseEquiv (encodeCentralRestricted022Word w r)))

theorem fine022Class_encodeCentral
    {n L G : ℕ} (w : CentralRestricted022Word 6 n L G)
    (r : Fin n) :
    fine022Class (encodeCentralRestricted022Word w r) = w.1.1 r := by
  by_cases h0 : w.1.1 r = (0 : Fin 3)
  · simp [encodeCentralRestricted022Word, fine022Class, h0]
  by_cases h1 : w.1.1 r = (1 : Fin 3)
  · simp [encodeCentralRestricted022Word, fine022Class, h1]
  have h2 : w.1.1 r = (2 : Fin 3) := by
    apply Fin.ext
    omega
  simp [encodeCentralRestricted022Word, fine022Class, h2]

theorem reverseOuterClass_eq_zero_iff (c : Fin 3) :
    reverseOuterClass c = (0 : Fin 3) ↔ c = (2 : Fin 3) := by
  fin_cases c <;> decide

theorem reverseOuterClass_eq_one_iff (c : Fin 3) :
    reverseOuterClass c = (1 : Fin 3) ↔ c = (1 : Fin 3) := by
  fin_cases c <;> decide

theorem reverseOuterClass_eq_two_iff (c : Fin 3) :
    reverseOuterClass c = (2 : Fin 3) ↔ c = (0 : Fin 3) := by
  fin_cases c <;> decide

theorem centralWordToRow9Pow_leftGrade (m : ℕ)
    (w : CentralRestricted022Word 6 (row9Length m)
      (row9OuterCount m) (row9MiddleCount m))
    (r : Fin (row9Length m)) :
    (PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r).leftGrade =
      reverseOuterClass (w.1.1 r) := by
  rw [show PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r =
      ULift.up (fine022CoarseEquiv (encodeCentralRestricted022Word w r)) from
    congrFun (PowIndex.get_ofFun (ι := LiftedCoarsePair.{u} 6 2) (row9Length m)
      (fun r ↦ ULift.up (fine022CoarseEquiv
        (encodeCentralRestricted022Word w r)))) r]
  change (fine022CoarseEquiv (encodeCentralRestricted022Word w r)).leftGrade = _
  rw [fine022Coarse_leftGrade, fine022Class_encodeCentral]

theorem centralWordToRow9Pow_allowed (m : ℕ)
    (w : CentralRestricted022Word 6 (row9Length m)
      (row9OuterCount m) (row9MiddleCount m)) :
    row9Allowed m (centralWordToRow9Pow.{u} m w) := by
  intro a
  fin_cases a
  · have hp := w.1.2 (2 : Fin 3)
    have htypes :
        {r : Fin (row9Length m) //
          (PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r).leftGrade =
            (0 : Fin 3)} =
          {r : Fin (row9Length m) // w.1.1 r = (2 : Fin 3)} := by
      congr 1
      funext r
      apply propext
      rw [centralWordToRow9Pow_leftGrade]
      exact reverseOuterClass_eq_zero_iff _
    change Fintype.card {r : Fin (row9Length m) //
        (PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r).leftGrade =
          (0 : Fin 3)} = row9OuterCount m
    calc
      Fintype.card {r : Fin (row9Length m) //
          (PowIndex.get (row9Length m)
            (centralWordToRow9Pow.{u} m w) r).leftGrade = (0 : Fin 3)} =
          Nat.card {r : Fin (row9Length m) //
            (PowIndex.get (row9Length m)
              (centralWordToRow9Pow.{u} m w) r).leftGrade = (0 : Fin 3)} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card {r : Fin (row9Length m) // w.1.1 r = (2 : Fin 3)} :=
        congrArg Nat.card htypes
      _ = Fintype.card {r : Fin (row9Length m) //
            w.1.1 r = (2 : Fin 3)} := Nat.card_eq_fintype_card
      _ = row9OuterCount m := by
        simpa only [centralSplitMultiplicity, row9OuterCount,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using hp
  · have hp := w.1.2 (1 : Fin 3)
    have htypes :
        {r : Fin (row9Length m) //
          (PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r).leftGrade =
            (1 : Fin 3)} =
          {r : Fin (row9Length m) // w.1.1 r = (1 : Fin 3)} := by
      congr 1
      funext r
      apply propext
      rw [centralWordToRow9Pow_leftGrade]
      exact reverseOuterClass_eq_one_iff _
    change Fintype.card {r : Fin (row9Length m) //
        (PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r).leftGrade =
          (1 : Fin 3)} = row9MiddleCount m
    calc
      Fintype.card {r : Fin (row9Length m) //
          (PowIndex.get (row9Length m)
            (centralWordToRow9Pow.{u} m w) r).leftGrade = (1 : Fin 3)} =
          Nat.card {r : Fin (row9Length m) //
            (PowIndex.get (row9Length m)
              (centralWordToRow9Pow.{u} m w) r).leftGrade = (1 : Fin 3)} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card {r : Fin (row9Length m) // w.1.1 r = (1 : Fin 3)} :=
        congrArg Nat.card htypes
      _ = Fintype.card {r : Fin (row9Length m) //
            w.1.1 r = (1 : Fin 3)} := Nat.card_eq_fintype_card
      _ = row9MiddleCount m := by
        simpa only [centralSplitMultiplicity, row9MiddleCount,
          Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons] using hp
  · have hp := w.1.2 (0 : Fin 3)
    have htypes :
        {r : Fin (row9Length m) //
          (PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r).leftGrade =
            (2 : Fin 3)} =
          {r : Fin (row9Length m) // w.1.1 r = (0 : Fin 3)} := by
      congr 1
      funext r
      apply propext
      rw [centralWordToRow9Pow_leftGrade]
      exact reverseOuterClass_eq_two_iff _
    change Fintype.card {r : Fin (row9Length m) //
        (PowIndex.get (row9Length m) (centralWordToRow9Pow.{u} m w) r).leftGrade =
          (2 : Fin 3)} = row9OuterCount m
    calc
      Fintype.card {r : Fin (row9Length m) //
          (PowIndex.get (row9Length m)
            (centralWordToRow9Pow.{u} m w) r).leftGrade = (2 : Fin 3)} =
          Nat.card {r : Fin (row9Length m) //
            (PowIndex.get (row9Length m)
              (centralWordToRow9Pow.{u} m w) r).leftGrade = (2 : Fin 3)} :=
        Nat.card_eq_fintype_card.symm
      _ = Nat.card {r : Fin (row9Length m) // w.1.1 r = (0 : Fin 3)} :=
        congrArg Nat.card htypes
      _ = Fintype.card {r : Fin (row9Length m) //
            w.1.1 r = (0 : Fin 3)} := Nat.card_eq_fintype_card
      _ = row9OuterCount m := by
        simpa only [centralSplitMultiplicity, row9OuterCount,
          Matrix.cons_val_zero] using hp

noncomputable def centralWordToRow9 (m : ℕ)
    (w : CentralRestricted022Word 6 (row9Length m)
      (row9OuterCount m) (row9MiddleCount m)) :
    row9AllowedWord.{u} m :=
  ⟨centralWordToRow9Pow m w, centralWordToRow9Pow_allowed m w⟩

theorem centralWordToRow9_injective (m : ℕ) :
    Function.Injective (centralWordToRow9.{u} m) := by
  intro w v h
  apply encodeCentralRestricted022Word_injective
  funext r
  have hp := congrArg Subtype.val h
  have hfun := congrArg
    (PowIndex.get (row9Length m)) hp
  have hr := congrFun hfun r
  have hgw := congrFun (PowIndex.get_ofFun (ι := LiftedCoarsePair.{u} 6 2)
    (row9Length m) (fun r ↦ ULift.up (fine022CoarseEquiv
      (encodeCentralRestricted022Word w r)))) r
  have hgv := congrFun (PowIndex.get_ofFun (ι := LiftedCoarsePair.{u} 6 2)
    (row9Length m) (fun r ↦ ULift.up (fine022CoarseEquiv
      (encodeCentralRestricted022Word v r)))) r
  have hr' :
      ULift.up (fine022CoarseEquiv (encodeCentralRestricted022Word w r)) =
        ULift.up (fine022CoarseEquiv (encodeCentralRestricted022Word v r)) :=
    hgw.symm.trans (hr.trans hgv)
  apply fine022CoarseEquiv.injective
  exact congrArg ULift.down hr'

theorem row9AllowedWord_card_eq_restricted022Word (m : ℕ) :
    Nat.card (row9AllowedWord.{u} m) =
      Nat.card (MME.DWZTable2Component022.Restricted022Word 6
        (row9Length m) (row9OuterCount m) (row9MiddleCount m)) := by
  apply Nat.le_antisymm
  · have h := Nat.card_le_card_of_injective (row9ToCentralWord.{u} m)
      (row9ToCentralWord_injective.{u} m)
    simpa [CentralRestricted022Word, CentralSplitPattern,
      centralSplitMultiplicity,
      MME.DWZTable2Component022.Restricted022Word,
      MME.DWZTable2Component022.SplitPattern,
      MME.DWZTable2Component022.splitMultiplicity] using h
  · have h := Nat.card_le_card_of_injective (centralWordToRow9.{u} m)
      (centralWordToRow9_injective.{u} m)
    simpa [CentralRestricted022Word, CentralSplitPattern,
      centralSplitMultiplicity,
      MME.DWZTable2Component022.Restricted022Word,
      MME.DWZTable2Component022.SplitPattern,
      MME.DWZTable2Component022.splitMultiplicity] using h

theorem row9AllowedWord_card_eq_table2Parameter (m : ℕ) :
    Nat.card (row9AllowedWord.{u} m) =
      Nat.card (MME.DWZTable2Component022.Restricted022Word 6
        (MME.DWZTable2Component022.table2Power022 (10366945 * m))
        (MME.DWZTable2Component022.table2OuterCount022 (10366945 * m))
        (MME.DWZTable2Component022.table2MiddleCount022
          (10366945 * m))) := by
  rw [row9AllowedWord_card_eq_restricted022Word]
  congr 3 <;>
    simp [row9Length, row9OuterCount, row9MiddleCount,
      MME.DWZTable2Counts.component, MME.DWZTable2Counts.split,
      MME.DWZTable2Component022.table2Power022,
      MME.DWZTable2Component022.table2OuterCount022,
      MME.DWZTable2Component022.table2MiddleCount022] <;>
    ring

end MME.DWZCentral022AllowedCard

open MME.DWZTable2Component022

theorem solution
    (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarsePair.{u} 6 2)
        (MME.DWZTable2Counts.component 9 * m) //
      componentWordAllowed (9 : Fin 15) m w} =
      Nat.card (Restricted022Word 6
        (table2Power022 (10366945 * m))
        (table2OuterCount022 (10366945 * m))
        (table2MiddleCount022 (10366945 * m))) := by
  exact MME.DWZCentral022AllowedCard.row9AllowedWord_card_eq_table2Parameter m
