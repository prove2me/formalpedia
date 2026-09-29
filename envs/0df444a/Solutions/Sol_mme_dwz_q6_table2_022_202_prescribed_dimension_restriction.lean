-- Prove2me | solution 1 for mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T03:35:09.639206+00:00
-- url     : https://prove2.me/submissions/8ff7bd97-2dd3-4e0a-84db-163302643d1a

import Mathlib
import Definitions.Def_mme_dwz_table2_component_022_word_data
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_square_canonical_central022_restrict
import Theorems.Thm_mme_CW_square_canonical_central202_restrict
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Theorems.Thm_mme_kronFin_MMObj_iso
import Theorems.Thm_mme_restrict_kronPow

open MME BigOperators
open MME.DWZSquare

set_option autoImplicit false

namespace MME.DWZTable2Component022

private def encodeRestrictedWord {q m L G : ℕ}
    (w : Restricted022Word q m L G) : Fin m → Fine022Channel q := fun r ↦
  if _h0 : w.1.1 r = (0 : Fin 3) then
    Sum.inl 0
  else if _h1 : w.1.1 r = (1 : Fin 3) then
    Sum.inr (Sum.inl (w.2 ⟨r, _h1⟩))
  else
    Sum.inr (Sum.inr 0)

private def fine022ChannelClass {q : ℕ} : Fine022Channel q → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

private theorem fine022ChannelClass_encode
    {q m L G : ℕ} (w : Restricted022Word q m L G) (r : Fin m) :
    fine022ChannelClass (encodeRestrictedWord w r) = w.1.1 r := by
  by_cases h0 : w.1.1 r = (0 : Fin 3)
  · simp [encodeRestrictedWord, fine022ChannelClass, h0]
  by_cases h1 : w.1.1 r = (1 : Fin 3)
  · simp [encodeRestrictedWord, fine022ChannelClass, h1]
  have h2 : w.1.1 r = (2 : Fin 3) := by
    apply Fin.ext
    omega
  simp [encodeRestrictedWord, fine022ChannelClass, h2]

private theorem encodeRestrictedWord_at_middle
    {q m L G : ℕ} (p : SplitPattern m L G)
    (label : {r : Fin m // p.1 r = (1 : Fin 3)} → Fin q × Fin q)
    (r : {r : Fin m // p.1 r = (1 : Fin 3)}) :
    encodeRestrictedWord ⟨p, label⟩ r.1 =
      Sum.inr (Sum.inl (label r)) := by
  simp [encodeRestrictedWord, r.2]
  rfl

private theorem encodeRestrictedWord_injective
    {q m L G : ℕ} :
    Function.Injective
      (encodeRestrictedWord : Restricted022Word q m L G →
        (Fin m → Fine022Channel q)) := by
  intro w v h
  have hp : w.1 = v.1 := by
    apply Subtype.ext
    funext r
    rw [← fine022ChannelClass_encode w r,
      ← fine022ChannelClass_encode v r, h]
  cases w with
  | mk wp wl =>
    cases v with
    | mk vp vl =>
      dsimp only at hp
      subst vp
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        funext r
        have hr := congrFun h r.1
        rw [encodeRestrictedWord_at_middle wp wl r,
          encodeRestrictedWord_at_middle wp vl r] at hr
        exact Sum.inl.inj (Sum.inr.inj hr)

/-- Cardinality comparison between prescribed-split words and all channel
words.  This is a combinatorial injection only; it is not a linear map on the
canonical CW-square block. -/
theorem restricted022Word_card_le_full (q m L G : ℕ) :
    Nat.card (Restricted022Word q m L G) ≤ (q ^ 2 + 2) ^ m := by
  have hcard := Nat.card_le_card_of_injective encodeRestrictedWord
    (encodeRestrictedWord_injective (q := q) (m := m) (L := L) (G := G))
  have hchannel : Nat.card (Fine022Channel q) = q ^ 2 + 2 := by
    simp [Fine022Channel]
    ring
  calc
    Nat.card (Restricted022Word q m L G) ≤
        Nat.card (Fin m → Fine022Channel q) := hcard
    _ = (q ^ 2 + 2) ^ m := by rw [Nat.card_fun, hchannel, Nat.card_fin]

/-- The matrix-dimension parameter predicted by the prescribed `L,G,L`
split. -/
def splitDimension (q m L G : ℕ) : ℕ :=
  splitWordCount m L * q ^ (2 * G)

/-- Cardinality of the literal fine-Z word type.  This is exactly the source
multinomial times the `q^2` choices at every middle position. -/
theorem restricted022Word_card
    (q m L G : ℕ) (hcount : 2 * L + G = m) :
    Nat.card (Restricted022Word q m L G) = splitDimension q m L G := by
  have hsum : ∑ c : Fin 3, splitMultiplicity L G c = m := by
    simp [splitMultiplicity, Fin.sum_univ_succ]
    omega
  let patternPredicate : (Fin m → Fin 3) → Prop := fun g ↦
    ∀ i, Fintype.card {a : Fin m // g a = i} = splitMultiplicity L G i
  letI patternDecidable : DecidablePred patternPredicate := fun _ ↦
    Fintype.decidableForallFintype
  letI patternFintype : Fintype {g : Fin m → Fin 3 // patternPredicate g} :=
    Subtype.fintype patternPredicate
  have hpattern0 :=
    mme_fintype_prescribed_fiber_function_card
      (α := Fin m) (ι := Fin 3) (splitMultiplicity L G) (by simpa using hsum)
  have hpatternNat0 :
      Nat.card
          {g : Fin m → Fin 3 // ∀ i,
            Fintype.card {a : Fin m // g a = i} = splitMultiplicity L G i} =
        m.factorial / ∏ i, (splitMultiplicity L G i).factorial := by
    calc
      Nat.card
          {g : Fin m → Fin 3 // ∀ i,
            Fintype.card {a : Fin m // g a = i} = splitMultiplicity L G i} =
          Fintype.card
            {g : Fin m → Fin 3 // ∀ i,
              Fintype.card {a : Fin m // g a = i} = splitMultiplicity L G i} :=
        Nat.card_eq_fintype_card
      _ = m.factorial / ∏ i, (splitMultiplicity L G i).factorial := by
        simpa using hpattern0
  have hpattern :
      Nat.card (SplitPattern m L G) =
        m.factorial / (L.factorial * G.factorial * L.factorial) := by
    simpa [SplitPattern, splitMultiplicity, Fin.prod_univ_succ, Nat.mul_assoc]
      using hpatternNat0
  have hLm : L ≤ m := by omega
  have hLrem : L ≤ m - L := by omega
  have hfirst := Nat.choose_mul_factorial_mul_factorial hLm
  have hsecond := Nat.choose_mul_factorial_mul_factorial hLrem
  rw [show m - L - L = G by omega] at hsecond
  have hfactorial :
      (L.factorial * G.factorial * L.factorial) * splitWordCount m L =
        m.factorial := by
    rw [splitWordCount]
    calc
      (L.factorial * G.factorial * L.factorial) *
            (Nat.choose m L * Nat.choose (m - L) L) =
          Nat.choose m L * L.factorial *
            (Nat.choose (m - L) L * L.factorial * G.factorial) := by ring
      _ = Nat.choose m L * L.factorial * (m - L).factorial := by rw [hsecond]
      _ = m.factorial := hfirst
  have hmultinomial :
      m.factorial / (L.factorial * G.factorial * L.factorial) =
        splitWordCount m L := by
    symm
    exact Nat.eq_div_of_mul_eq_right (by positivity) hfactorial
  have hmiddle (p : SplitPattern m L G) :
      Nat.card ({r : Fin m // p.1 r = (1 : Fin 3)} → Fin q × Fin q) =
        q ^ (2 * G) := by
    have hp := p.2 (1 : Fin 3)
    simp [splitMultiplicity] at hp
    have hpNat : Nat.card {r : Fin m // p.1 r = (1 : Fin 3)} = G := by
      rw [Nat.card_eq_fintype_card]
      exact hp
    rw [Nat.card_fun, Nat.card_prod, hpNat]
    simp only [Nat.card_fin]
    rw [show q * q = q ^ 2 by ring]
    rw [← pow_mul]
  letI : Fintype (SplitPattern m L G) := Fintype.ofFinite _
  unfold Restricted022Word
  rw [Nat.card_sigma]
  simp_rw [hmiddle]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    ← Nat.card_eq_fintype_card, hpattern, hmultinomial]
  rfl

private theorem mm022_power_iso
    {K : Type*} [Field K] (q m : ℕ) :
    TensorObj.Isomorphic
      ((MMObj K 1 1 (q ^ 2 + 2)).kronPow m)
      (MMObj K 1 1 ((q ^ 2 + 2) ^ m)) := by
  have heq :
      (MMObj K 1 1 (q ^ 2 + 2)).kronPow m =
        TensorObj.kronFin m (fun _ => MMObj K 1 1 (q ^ 2 + 2)) := by
    induction m with
    | zero => rfl
    | succ m ih => simp only [TensorObj.kronPow, TensorObj.kronFin, ih]
  rw [heq]
  have h := mme_kronFin_MMObj_iso (K := K) m
    (fun _ => 1) (fun _ => 1) (fun _ => q ^ 2 + 2)
  simp_rw [Fin.prod_const] at h
  simpa only [one_pow] using h

private theorem mm202_power_iso
    {K : Type*} [Field K] (q m : ℕ) :
    TensorObj.Isomorphic
      ((MMObj K (q ^ 2 + 2) 1 1).kronPow m)
      (MMObj K ((q ^ 2 + 2) ^ m) 1 1) := by
  have heq :
      (MMObj K (q ^ 2 + 2) 1 1).kronPow m =
        TensorObj.kronFin m (fun _ => MMObj K (q ^ 2 + 2) 1 1) := by
    induction m with
    | zero => rfl
    | succ m ih => simp only [TensorObj.kronPow, TensorObj.kronFin, ih]
  rw [heq]
  have h := mme_kronFin_MMObj_iso (K := K) m
    (fun _ => q ^ 2 + 2) (fun _ => 1) (fun _ => 1)
  simp_rw [Fin.prod_const] at h
  simpa only [one_pow] using h

/-- Dimension-level tensor extraction whose matrix dimension is the
cardinality of the prescribed-word type.

The proof uses only the cardinal inequality
`Nat.card (Restricted022Word q m L G) ≤ (q^2+2)^m`, followed by
`MMObj_restrict_of_le`.  It therefore does **not** identify the selected
matrix coordinates with `encodeRestrictedWord`, and it does not expose a
shared label-preserving zeroing for 022 and 202. -/
theorem central022_202_split_dimension_restrict
    {K : Type*} [Field K]
    (q m L G : ℕ) :
    TensorObj.Restrict
      (MMObj K 1 1 (Nat.card (Restricted022Word q m L G)))
      (((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 2 2)).kronPow m) ∧
    TensorObj.Restrict
      (MMObj K (Nat.card (Restricted022Word q m L G)) 1 1)
      (((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 0 2)).kronPow m) := by
  have hdim := restricted022Word_card_le_full q m L G
  constructor
  · exact TensorObj.Restrict.trans
      (MMObj_restrict_of_le (K := K) (by omega) (by omega) hdim)
      (TensorObj.Restrict.trans (mm022_power_iso (K := K) q m).2
        (mme_restrict_kronPow
          (mme_CW_square_canonical_central022_restrict (K := K) q) m))
  · exact TensorObj.Restrict.trans
      (MMObj_restrict_of_le (K := K) hdim (by omega) (by omega))
      (TensorObj.Restrict.trans (mm202_power_iso (K := K) q m).2
        (mme_restrict_kronPow
          (mme_CW_square_canonical_central202_restrict (K := K) q) m))

/-- Dimension-level 022/202 extraction with the exact multinomial-times-`q`
dimension predicted by the prescribed split.  This closes the cardinal
formula, but retains the channel-alignment limitation of
`central022_202_split_dimension_restrict`. -/
theorem central022_202_prescribed_split_dimension_restrict
    {K : Type*} [Field K]
    (q m L G : ℕ) (hcount : 2 * L + G = m) :
    TensorObj.Restrict
      (MMObj K 1 1 (splitDimension q m L G))
      (((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 0 2 2)).kronPow m) ∧
    TensorObj.Restrict
      (MMObj K (splitDimension q m L G) 1 1)
      (((cwSquareCanonicalGrading K q).blockSubtensor
        (cwSquareBlockType 2 0 2)).kronPow m) := by
  simpa only [restricted022Word_card q m L G hcount] using
    (central022_202_split_dimension_restrict (K := K) q m L G)

/-! ## Exact Table-2 specialization and `componentBase` normalization -/

theorem table2_022_counts_sum (t : ℕ) :
    2 * table2OuterCount022 t + table2MiddleCount022 t = table2Power022 t := by
  simp [table2OuterCount022, table2MiddleCount022, table2Power022]
  omega

private theorem table2_022_outer_ratio (t : ℕ) (ht : 0 < t) :
    ((table2OuterCount022 t : ℕ) : ℝ) /
        ((table2Power022 t : ℕ) : ℝ) = splitA := by
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  simp only [table2OuterCount022, table2Power022, Nat.cast_mul]
  dsimp only [splitA]
  field_simp [htR]
  ring

private theorem table2_022_middle_ratio (t : ℕ) (ht : 0 < t) :
    ((table2MiddleCount022 t : ℕ) : ℝ) /
        ((table2Power022 t : ℕ) : ℝ) = 1 - 2 * splitA := by
  have htR : (t : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ht)
  simp only [table2MiddleCount022, table2Power022, Nat.cast_mul]
  dsimp only [splitA]
  field_simp [htR]
  ring

private theorem table2_022_componentBase_normalized
    (tau : ℝ) (t : ℕ) (ht : 0 < t) :
    let m := table2Power022 t
    let L := table2OuterCount022 t
    let G := table2MiddleCount022 t
    let normalizedBase : ℝ :=
      Real.rpow
        (Real.rpow 6 (2 * ((G : ℝ) / (m : ℝ))) /
          (Real.rpow ((L : ℝ) / (m : ℝ))
              (2 * ((L : ℝ) / (m : ℝ))) *
            Real.rpow ((G : ℝ) / (m : ℝ))
              ((G : ℝ) / (m : ℝ)))) tau
    componentBase tau (9 : Fin 15) = normalizedBase ∧
      componentBase tau (10 : Fin 15) = normalizedBase := by
  dsimp only
  rw [table2_022_outer_ratio t ht, table2_022_middle_ratio t ht]
  constructor <;> simp [componentBase]

/-- Table-2 022/202 dimension-level leaf.  It proves genuine tensor
restrictions of the exact prescribed-word cardinality, closes that
cardinality to the multinomial/MM formula, and separately unfolds the scalar
normalization used by `DWZSquare.componentBase` at indices 9 and 10.

This theorem intentionally does not claim that its restriction maps are the
fine-Z projectors indexed by `Restricted022Word`, nor does it prove the
Stirling/entropy limit connecting the finite dimensions to the asymptotic
component value. -/
theorem dimensionSolution
    {K : Type*} [Field K] (tau : ℝ) (t : ℕ) (ht : 0 < t) :
    let m := table2Power022 t
    let L := table2OuterCount022 t
    let G := table2MiddleCount022 t
    let D := Nat.card (Restricted022Word 6 m L G)
    let normalizedBase : ℝ :=
      Real.rpow
        (Real.rpow 6 (2 * ((G : ℝ) / (m : ℝ))) /
          (Real.rpow ((L : ℝ) / (m : ℝ))
              (2 * ((L : ℝ) / (m : ℝ))) *
            Real.rpow ((G : ℝ) / (m : ℝ))
              ((G : ℝ) / (m : ℝ)))) tau
    (TensorObj.Restrict
        (MMObj K 1 1 D)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 0 2 2)).kronPow m) ∧
      TensorObj.Restrict
        (MMObj K D 1 1)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 2 0 2)).kronPow m)) ∧
    D = splitWordCount m L * 6 ^ (2 * G) ∧
    componentBase tau (9 : Fin 15) = normalizedBase ∧
    componentBase tau (10 : Fin 15) = normalizedBase := by
  dsimp only
  have hcount := table2_022_counts_sum t
  have hrestrict :=
    central022_202_split_dimension_restrict (K := K) 6
      (table2Power022 t) (table2OuterCount022 t) (table2MiddleCount022 t)
  have hcard := restricted022Word_card 6
    (table2Power022 t) (table2OuterCount022 t) (table2MiddleCount022 t) hcount
  have hbase := table2_022_componentBase_normalized tau t ht
  exact ⟨hrestrict, hcard, hbase⟩

end MME.DWZTable2Component022

open MME.DWZTable2Component022

universe u

/-- Top-level Prove2Me wrapper for the dimension-level Table-2 leaf. -/
theorem solution
    {K : Type u} [Field K] (tau : ℝ) (t : ℕ) (ht : 0 < t) :
    let m := table2Power022 t
    let L := table2OuterCount022 t
    let G := table2MiddleCount022 t
    let D := Nat.card (Restricted022Word 6 m L G)
    let normalizedBase : ℝ :=
      Real.rpow
        (Real.rpow 6 (2 * ((G : ℝ) / (m : ℝ))) /
          (Real.rpow ((L : ℝ) / (m : ℝ))
              (2 * ((L : ℝ) / (m : ℝ))) *
            Real.rpow ((G : ℝ) / (m : ℝ))
              ((G : ℝ) / (m : ℝ)))) tau
    (TensorObj.Restrict
        (MMObj K 1 1 D)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 0 2 2)).kronPow m) ∧
      TensorObj.Restrict
        (MMObj K D 1 1)
        (((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 2 0 2)).kronPow m)) ∧
    D = splitWordCount m L * 6 ^ (2 * G) ∧
    componentBase tau (9 : Fin 15) = normalizedBase ∧
    componentBase tau (10 : Fin 15) = normalizedBase :=
  MME.DWZTable2Component022.dimensionSolution tau t ht
