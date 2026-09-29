-- Prove2me | solution 1 for mme_dwz_table2_claim6_8_useful_brokenCopy_seven_eighths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:38:03.18201+00:00
-- url     : https://prove2.me/submissions/8aef79b7-715a-41f1-b076-b1856181484e

import Theorems.Thm_mme_dwz_table2_claim6_8_uniform_common_prime
import Theorems.Thm_mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
import Theorems.Thm_mme_dwz_step2_exists_broken_copy_seven_eighths
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible

open BigOperators

set_option autoImplicit false
set_option warningAsError true

namespace MME.DWZStep2UsefulCore

private abbrev Position (m : ℕ) := Fin (MME.DWZTable2Counts.scale * m)

private def regionOfShape :
    Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
  if h : MME.DWZSquare.shapeX s = 0 ∨ MME.DWZSquare.shapeY s = 0 then
    Sum.inl ⟨s, h⟩
  else
    Sum.inr (MME.DWZSquare.shapeZ s)

private abbrev Outer (m : ℕ) (K : Position m → Fin 5) :=
  {w : Position m → Fin 15 //
    (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
    ∀ s, Fintype.card {t : Position m // w t = s} =
      MME.DWZTable2Counts.component s * m}

private abbrev Typical (m : ℕ) (K : Position m → Fin 5) :=
  {small : Position m → Fin 3 × Fin 3 //
    (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
    ∀ q, Fintype.card {t : Position m // small t = q} =
      MME.DWZTable2Counts.gamma q * m}

private abbrev Compatible {m : ℕ} {K : Position m → Fin 5}
    (I : Outer m K) (small : Typical m K) : Prop :=
  ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
    Fintype.card
        {t : Position m //
          regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
      MME.DWZTable2Cardinality.cellCount m r a

private abbrev Useful (m : ℕ) {K : Position m → Fin 5}
    (retained : Outer m K) :=
  MME.DWZTable2StandardForm.UsefulBlock m retained.1

private noncomputable def smallOfUseful
    (m : ℕ) {K : Position m → Fin 5} (retained : Outer m K)
    (z : Useful m retained) : Typical m K := by
  classical
  refine ⟨z.1, ?_,
    (mme_dwz_table2_useful_block_typical_and_compatible
      m retained.1 z).1⟩
  intro t
  exact (z.2.1 t).trans (retained.2.1 t)

private theorem smallOfUseful_compatible
    (m : ℕ) {K : Position m → Fin 5} (retained : Outer m K)
    (z : Useful m retained) :
    Compatible retained (smallOfUseful m retained z) := by
  classical
  exact
    (mme_dwz_table2_useful_block_typical_and_compatible
      m retained.1 z).2

private abbrev N (m : ℕ) := MME.DWZTable2Counts.scale * m - 1

private def reindex (m : ℕ) (hm : 0 < m) : Fin (N m + 1) ≃ Position m :=
  finCongr (by
    exact Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))

private abbrev Weight (m p : ℕ) := Fin (N m + 1) → ZMod p

private def addressX (m : ℕ) (hm : 0 < m)
    {K : Position m → Fin 5} (I : Outer m K) : Fin (N m + 1) → Fin 5 :=
  fun t ↦ MME.DWZSquare.shapeX (I.1 (reindex m hm t))

private def addressZ (m : ℕ) (hm : 0 < m)
    (K : Position m → Fin 5) : Fin (N m + 1) → Fin 5 :=
  fun t ↦ K (reindex m hm t)

private def hX {m p : ℕ} (b0 : ZMod p) (w : Weight m p)
    (A : Fin (N m + 1) → Fin 5) : ZMod p :=
  b0 + ∑ t, ((A t).val : ZMod p) * w t

private def hZ {m p : ℕ} (b0 w0 : ZMod p) (w : Weight m p)
    (C : Fin (N m + 1) → Fin 5) : ZMod p :=
  b0 + (2 : ZMod p)⁻¹ *
    (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)

private def conditionedW0 (m : ℕ) (hm : 0 < m) {p : ℕ}
    {K : Position m → Fin 5} (retained : Outer m K)
    (w : Weight m p) : ZMod p :=
  2 * (∑ t, ((addressX m hm retained t).val : ZMod p) * w t) -
    ∑ t, ((4 : ZMod p) - (addressZ m hm K t).val) * w t

private abbrev hashRetained (m : ℕ) (hm : 0 < m) {p : ℕ}
    (b0 : ZMod p) {K : Position m → Fin 5} (retained A : Outer m K)
    (w : Weight m p) : Prop :=
  hX b0 w (addressX m hm A) =
    hZ b0 (conditionedW0 m hm retained w) w (addressZ m hm K)

private theorem retained_hash
    (m : ℕ) (hm : 0 < m) {p : ℕ} [Fact p.Prime]
    (hpodd : Odd p) (b0 : ZMod p)
    {K : Position m → Fin 5} (retained : Outer m K) :
    ∀ w : Weight m p, hashRetained m hm b0 retained retained w := by
  intro w
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have htwo : (2 : ZMod p)⁻¹ * 2 = 1 :=
    ZMod.inv_mul_of_unit 2 hunit
  simp only [hashRetained, hX, hZ, conditionedW0]
  rw [sub_add_cancel]
  calc
    b0 + ∑ t, ((addressX m hm retained t).val : ZMod p) * w t =
        b0 + 1 * (∑ t,
          ((addressX m hm retained t).val : ZMod p) * w t) := by ring
    _ = b0 + ((2 : ZMod p)⁻¹ * 2) *
        (∑ t, ((addressX m hm retained t).val : ZMod p) * w t) := by
          rw [htwo]
    _ = b0 + (2 : ZMod p)⁻¹ *
        (2 * (∑ t,
          ((addressX m hm retained t).val : ZMod p) * w t)) := by ring

private theorem fixed_prime_useful_survival
    (m : ℕ) (hm : 0 < m)
    (K : Position m → Fin 5)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlevel : 4 < p)
    (retained : Outer m K) (b0 : ZMod p)
    (hbudget : ∀ z : Useful m retained,
      8 * (Finset.univ.filter (fun A : Outer m K ↦
        A ≠ retained ∧ Compatible A (smallOfUseful m retained z))).card ≤ p) :
    ∃ w : Weight m p,
      7 * Fintype.card (Useful m retained) ≤
        8 * (MME.DWZStep2.brokenCopy
          (fun z A ↦
            Compatible A (smallOfUseful m retained z) ∧
              hashRetained m hm b0 retained A w)
          (fun _ _ ↦ True) retained).nonholes.card := by
  classical
  have hpointwise : ∀ z : Useful m retained,
      8 * (Finset.univ.filter (fun w : Weight m p ↦
        1 < (Finset.univ.filter (fun A : Outer m K ↦
          Compatible A (smallOfUseful m retained z) ∧
            hashRetained m hm b0 retained A w)).card)).card ≤
        Fintype.card (Weight m p) := by
    intro z
    have h := mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
      m hm K hpodd hlevel b0 retained (smallOfUseful m retained z)
        (smallOfUseful_compatible m retained z) (hbudget z)
    simpa only [Position, N, Weight, Compatible, regionOfShape,
      hashRetained, hX, hZ, conditionedW0, addressX, addressZ,
      reindex] using h
  exact mme_dwz_step2_exists_broken_copy_seven_eighths
    (fun z A ↦ Compatible A (smallOfUseful m retained z))
    (fun _ _ ↦ True) (hashRetained m hm b0 retained) retained
    (fun _ ↦ trivial) (smallOfUseful_compatible m retained)
    (retained_hash m hm hpodd b0 retained) hpointwise

private theorem common_prime_useful_survival_core
    (m : ℕ) (hm : 0 < m) (d : ℕ) :
    ∃ K : Position m → Fin 5,
      (∀ k, Fintype.card {t : Position m // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
      Nonempty (Outer m K) ∧ Nonempty (Typical m K) ∧
      ∃ D p : ℕ, ∃ hp : p.Prime,
        letI : Fact p.Prime := ⟨hp⟩
        (∀ retained small,
          (Finset.univ.filter (fun A : Outer m K ↦
            A ≠ retained ∧ Compatible A small)).card ≤ D) ∧
        (D : ℝ) ≤
          (6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
            (Nat.card (Outer m K) : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ∧
        Odd p ∧ 4 < p ∧ 8 * d ≤ p ∧
        (∀ retained small,
          8 * (Finset.univ.filter (fun A : Outer m K ↦
            A ≠ retained ∧ Compatible A small)).card ≤ p) ∧
        max 4 (8 * max d D) < p ∧
        p ≤ 2 * max 4 (8 * max d D) ∧
        (p : ℝ) ≤ max 8 (16 * max (d : ℝ)
          ((6 * (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ^ 9 *
            (Nat.card (Outer m K) : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP))) ∧
        (∀ (retained : Outer m K) (b0 : ZMod p),
          ∃ w : Weight m p,
            7 * Fintype.card (Useful m retained) ≤
              8 * (MME.DWZStep2.brokenCopy
                (fun z A ↦
                  Compatible A (smallOfUseful m retained z) ∧
                    hashRetained m hm b0 retained A w)
                (fun _ _ ↦ True) retained).nonholes.card) := by
  classical
  obtain ⟨K, hK, hOuter, hTypical, D, p, hD, hDR, hp, hpodd,
      hlevel, hfirst, hbudget, hlower, hupper, hpRate⟩ :=
    mme_dwz_table2_claim6_8_uniform_common_prime m d
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨K, hK, hOuter, hTypical, D, p, hp,
    hD, hDR, hpodd, hlevel, hfirst, hbudget,
    hlower, hupper, hpRate, ?_⟩
  intro retained b0
  apply fixed_prime_useful_survival m hm K hpodd hlevel retained b0
  intro z
  exact hbudget retained (smallOfUseful m retained z)

end MME.DWZStep2UsefulCore

theorem solution
    (m : ℕ) (hm : 0 < m) (d : ℕ) :
    ∃ K : Fin (MME.DWZTable2Counts.scale * m) → Fin 5,
      let sourceLength := MME.DWZTable2Counts.scale * m
      let n := sourceLength - 1
      let reindex : Fin (n + 1) ≃ Fin sourceLength :=
        finCongr (by
          dsimp only [n, sourceLength]
          exact Nat.sub_add_cancel
            (Nat.one_le_iff_ne_zero.mpr
              (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
      let regionOfShape :
          Fin 15 → MME.DWZTable2Cardinality.SplitRegion := fun s ↦
        if h : MME.DWZSquare.shapeX s = 0 ∨
            MME.DWZSquare.shapeY s = 0 then
          Sum.inl ⟨s, h⟩
        else
          Sum.inr (MME.DWZSquare.shapeZ s)
      let Outer :=
        {w : Fin sourceLength → Fin 15 //
          (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
          ∀ s, Fintype.card {t : Fin sourceLength // w t = s} =
            MME.DWZTable2Counts.component s * m}
      let Typical :=
        {small : Fin sourceLength → Fin 3 × Fin 3 //
          (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
          ∀ q, Fintype.card {t : Fin sourceLength // small t = q} =
            MME.DWZTable2Counts.gamma q * m}
      let Compatible : Outer → Typical → Prop := fun I small ↦
        ∀ (r : MME.DWZTable2Cardinality.SplitRegion) (a : Fin 3),
          Fintype.card
              {t : Fin sourceLength //
                regionOfShape (I.1 t) = r ∧ (small.1 t).1 = a} =
            MME.DWZTable2Cardinality.cellCount m r a
      let candidates : Outer → Typical → Finset Outer := fun retained small ↦
        Finset.univ.filter
          (fun A : Outer ↦ A ≠ retained ∧ Compatible A small)
      let R : ℝ :=
        (6 * (((sourceLength + 1 : ℕ) : ℝ))) ^ 9 *
          (Nat.card Outer : ℝ) *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              MME.DWZSquare.logAlphaP)
      (∀ k, Fintype.card {t : Fin sourceLength // K t = k} =
          MME.DWZTable2Counts.alphaZ k * m) ∧
        Nonempty Outer ∧ Nonempty Typical ∧
        ∃ D p : ℕ, ∃ hp : p.Prime,
          letI : Fact p.Prime := ⟨hp⟩
          (∀ retained small, (candidates retained small).card ≤ D) ∧
          (D : ℝ) ≤ R ∧
          Odd p ∧ 4 < p ∧ 8 * d ≤ p ∧
          (∀ retained small,
            8 * (candidates retained small).card ≤ p) ∧
          max 4 (8 * max d D) < p ∧
          p ≤ 2 * max 4 (8 * max d D) ∧
          (p : ℝ) ≤ max 8 (16 * max (d : ℝ) R) ∧
          ∀ (retained : Outer) (b0 : ZMod p),
            let Block :=
              MME.DWZTable2StandardForm.UsefulBlock m retained.1
            let addressX : Outer → Fin (n + 1) → Fin 5 := fun I t ↦
              MME.DWZSquare.shapeX (I.1 (reindex t))
            let addressZ : Fin (n + 1) → Fin 5 := fun t ↦ K (reindex t)
            let hX : (Fin (n + 1) → ZMod p) →
                (Fin (n + 1) → Fin 5) → ZMod p := fun w A ↦
              b0 + ∑ t, ((A t).val : ZMod p) * w t
            let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
                (Fin (n + 1) → Fin 5) → ZMod p := fun w0 w C ↦
              b0 + (2 : ZMod p)⁻¹ *
                (w0 + ∑ t, ((4 : ZMod p) - (C t).val) * w t)
            let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p :=
              fun w ↦
                2 * (∑ t,
                  ((addressX retained t).val : ZMod p) * w t) -
                  ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
            let hashRetained :
                Outer → (Fin (n + 1) → ZMod p) → Prop := fun A w ↦
              hX w (addressX A) = hZ (conditionedW0 w) w addressZ
            ∃ smallOf : Block → Typical,
              (∀ z : Block,
          (smallOf z).1 = z.1 ∧ Compatible retained (smallOf z)) ∧
              ∃ w : Fin (n + 1) → ZMod p,
                7 * Fintype.card Block ≤
                  8 * (MME.DWZStep2.brokenCopy
                    (fun z A ↦
                      Compatible A (smallOf z) ∧ hashRetained A w)
                    (fun _ _ ↦ True) retained).nonholes.card := by
  classical
  obtain ⟨K, hK, hOuter, hTypical, D, p, hp, hD, hDR, hpodd,
      hlevel, hfirst, hbudget, hlower, hupper, hpRate, hsurvive⟩ :=
    MME.DWZStep2UsefulCore.common_prime_useful_survival_core m hm d
  refine ⟨K, ?_⟩
  dsimp only
  let : Fact p.Prime := ⟨hp⟩
  refine ⟨hK, hOuter, hTypical, D, p, hp, ?_, ?_, hpodd, hlevel,
    hfirst, ?_, hlower, hupper, ?_, ?_⟩
  · exact hD
  · simpa only [MME.DWZStep2UsefulCore.Outer] using hDR
  · exact hbudget
  · simpa only [MME.DWZStep2UsefulCore.Outer] using hpRate
  · intro retained b0
    refine ⟨MME.DWZStep2UsefulCore.smallOfUseful m retained, ?_, ?_⟩
    · intro z
      exact ⟨rfl,
        MME.DWZStep2UsefulCore.smallOfUseful_compatible m retained z⟩
    · have hs := hsurvive retained b0
      exact hs
