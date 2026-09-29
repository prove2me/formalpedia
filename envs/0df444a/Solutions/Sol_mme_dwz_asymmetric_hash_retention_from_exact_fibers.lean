-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_retention_from_exact_fibers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T03:54:22.091814+00:00
-- url     : https://prove2.me/submissions/00f62e47-147f-49aa-a178-0e4cc0fb432e

import Mathlib
import Theorems.Thm_mme_finset_incidence_double_count
import Theorems.Thm_mme_finite_collision_budget_averaging_real

open BigOperators
set_option autoImplicit false
set_option warningAsError true

private theorem mme_dwz_target_two_mode_collision_card_le_of_degree
    {Edge X Y : Type}
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y) (d : ℕ)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d) :
    ((T.product A).filter (fun p ↦
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card ≤
        2 * T.card * d := by
  classical
  let CX := (T.product A).filter (fun p ↦ x p.1 = x p.2)
  let CY := (T.product A).filter (fun p ↦ y p.1 = y p.2)
  let FX : Edge → Finset (Edge × Edge) := fun a ↦
    (A.filter (fun b ↦ x b = x a)).image (fun b ↦ (a, b))
  let FY : Edge → Finset (Edge × Edge) := fun a ↦
    (A.filter (fun b ↦ y b = y a)).image (fun b ↦ (a, b))
  have hCX : CX = T.biUnion FX := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hpProd := Finset.mem_product.mp hp'.1
      refine Finset.mem_biUnion.mpr ⟨p.1, hpProd.1, ?_⟩
      exact Finset.mem_image.mpr ⟨p.2,
        Finset.mem_filter.mpr ⟨hpProd.2, hp'.2.symm⟩, rfl⟩
    · intro hp
      obtain ⟨a, haT, hpFX⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨b, hb, hpab⟩ := Finset.mem_image.mp hpFX
      rw [← hpab]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨haT, (Finset.mem_filter.mp hb).1⟩,
          (Finset.mem_filter.mp hb).2.symm⟩
  have hCY : CY = T.biUnion FY := by
    ext p
    constructor
    · intro hp
      have hp' := Finset.mem_filter.mp hp
      have hpProd := Finset.mem_product.mp hp'.1
      refine Finset.mem_biUnion.mpr ⟨p.1, hpProd.1, ?_⟩
      exact Finset.mem_image.mpr ⟨p.2,
        Finset.mem_filter.mpr ⟨hpProd.2, hp'.2.symm⟩, rfl⟩
    · intro hp
      obtain ⟨a, haT, hpFY⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨b, hb, hpab⟩ := Finset.mem_image.mp hpFY
      rw [← hpab]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨haT, (Finset.mem_filter.mp hb).1⟩,
          (Finset.mem_filter.mp hb).2.symm⟩
  have hFX : ∀ a ∈ T, (FX a).card ≤ d := by
    intro a ha
    calc
      (FX a).card ≤ (A.filter (fun b ↦ x b = x a)).card :=
        Finset.card_image_le
      _ ≤ d := hx a ha
  have hFY : ∀ a ∈ T, (FY a).card ≤ d := by
    intro a ha
    calc
      (FY a).card ≤ (A.filter (fun b ↦ y b = y a)).card :=
        Finset.card_image_le
      _ ≤ d := hy a ha
  have hCXcard : CX.card ≤ T.card * d := by
    rw [hCX]
    exact Finset.card_biUnion_le_card_mul T FX d hFX
  have hCYcard : CY.card ≤ T.card * d := by
    rw [hCY]
    exact Finset.card_biUnion_le_card_mul T FY d hFY
  have hsub :
      (T.product A).filter (fun p ↦
        p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2)) ⊆ CX ∪ CY := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    rcases hp'.2.2 with hpx | hpy
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp'.1, hpx⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp'.1, hpy⟩)
  calc
    ((T.product A).filter (fun p ↦
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))).card
        ≤ (CX ∪ CY).card := Finset.card_le_card hsub
    _ ≤ CX.card + CY.card := Finset.card_union_le CX CY
    _ ≤ T.card * d + T.card * d := Nat.add_le_add hCXcard hCYcard
    _ = 2 * T.card * d := by ring

private theorem mme_dwz_target_two_mode_isolation_pruning
    {Edge X Y : Type}
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (E T : Finset Edge) (hTE : T ⊆ E)
    (x : Edge → X) (y : Edge → Y) :
    let C := (T.product E).filter (fun p ↦
      p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))
    ∃ I : Finset Edge,
      I ⊆ T ∧
      I ⊆ E ∧
      (∀ e ∈ I, ∀ e' ∈ E,
        x e = x e' ∨ y e = y e' → e = e') ∧
      T.card ≤ I.card + C.card := by
  classical
  let Isolated : Edge → Prop := fun e ↦
    ∀ e' ∈ E, x e = x e' ∨ y e = y e' → e = e'
  let I := T.filter Isolated
  let C := (T.product E).filter (fun p ↦
    p.1 ≠ p.2 ∧ (x p.1 = x p.2 ∨ y p.1 = y p.2))
  have hIT : I ⊆ T := Finset.filter_subset _ _
  have hnot (e : Edge) (he : e ∈ T \ I) : ¬ Isolated e := by
    have he' := Finset.mem_sdiff.mp he
    intro hiso
    exact he'.2 (Finset.mem_filter.mpr ⟨he'.1, hiso⟩)
  have hcompetitor (e : Edge) (he : e ∈ T \ I) :
      ∃ e' ∈ E, e ≠ e' ∧ (x e = x e' ∨ y e = y e') := by
    have hn := hnot e he
    simp only [Isolated] at hn
    push Not at hn
    obtain ⟨e', he'E, hshare, hne⟩ := hn
    exact ⟨e', he'E, hne, hshare⟩
  let competitor : Edge → Edge := fun e ↦
    if he : e ∈ T \ I then Classical.choose (hcompetitor e he) else e
  have hcompetitor_spec (e : Edge) (he : e ∈ T \ I) :
      competitor e ∈ E ∧ e ≠ competitor e ∧
        (x e = x (competitor e) ∨ y e = y (competitor e)) := by
    simp only [competitor, dif_pos he]
    exact ⟨(Classical.choose_spec (hcompetitor e he)).1,
      (Classical.choose_spec (hcompetitor e he)).2.1,
      (Classical.choose_spec (hcompetitor e he)).2.2⟩
  let f : Edge → Edge × Edge := fun e ↦ (e, competitor e)
  have hmaps : Set.MapsTo f (↑(T \ I) : Set Edge)
      (↑C : Set (Edge × Edge)) := by
    intro e he
    have heFin : e ∈ T \ I := he
    have he' := Finset.mem_sdiff.mp heFin
    have hs := hcompetitor_spec e heFin
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨he'.1, hs.1⟩,
      hs.2.1, hs.2.2⟩
  have hinj : Set.InjOn f (↑(T \ I) : Set Edge) := by
    intro a ha b hb hab
    exact congrArg Prod.fst hab
  have hdeleted : (T \ I).card ≤ C.card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  refine ⟨I, hIT, fun e he ↦ hTE (hIT he), ?_, ?_⟩
  · intro e heI e' he'E hshare
    exact (Finset.mem_filter.mp heI).2 e' he'E hshare
  · change T.card ≤ I.card + C.card
    have hpartition := Finset.card_sdiff_add_card_eq_card hIT
    omega

private theorem mme_dwz_asymmetric_hash_normalized_half_budget
    (N p T S d : ℕ) (hp : 0 < p) (hmod : 4 * d ≤ p) :
    (p : ℝ) ^ (N + 3) *
          (((T : ℝ) * (S : ℝ)) / (2 * (p : ℝ) ^ 2)) +
        (2 * T * d * S : ℕ) * (p : ℝ) ^ N ≤
      (T * S : ℕ) * (p : ℝ) ^ (N + 1) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hpR
  have hmodR : (4 : ℝ) * (d : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast hmod
  have hfirst :
      (p : ℝ) ^ (N + 3) *
          (((T : ℝ) * (S : ℝ)) / (2 * (p : ℝ) ^ 2)) =
        ((T : ℝ) * (S : ℝ) * (p : ℝ) ^ (N + 1)) / 2 := by
    rw [show N + 3 = (N + 1) + 2 by omega, pow_add]
    field_simp
  rw [hfirst]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [show N + 1 = N + 1 by rfl, pow_succ]
  have hP : 0 ≤ (p : ℝ) ^ N := by positivity
  have hT : 0 ≤ (T : ℝ) := by positivity
  have hS : 0 ≤ (S : ℝ) := by positivity
  nlinarith [mul_nonneg (mul_nonneg hT hS) hP]

private theorem mme_dwz_asymmetric_hash_exact_incidence_sums
    {Ω Edge X Y : Type}
    [Fintype Ω] [DecidableEq Ω]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (E : Ω → Finset Edge) (N p B : ℕ)
    (hE : ∀ ω, E ω ⊆ A)
    (hsingle : ∀ a ∈ T,
      (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card =
        B * p ^ (N + 1))
    (hpair : ∀ q ∈ (T.product A).filter (fun q ↦
        q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2)),
      (Finset.univ.filter (fun ω : Ω ↦
        q.1 ∈ E ω ∧ q.2 ∈ E ω)).card ≤
          B * p ^ N) :
    (∑ ω, (T.filter (fun a ↦ a ∈ E ω)).card) =
        T.card * B * p ^ (N + 1) ∧
      (∑ ω, (((T.filter (fun a ↦ a ∈ E ω)).product (E ω)).filter
        (fun q ↦ q.1 ≠ q.2 ∧
          (x q.1 = x q.2 ∨ y q.1 = y q.2))).card) ≤
        ((T.product A).filter (fun q ↦ q.1 ≠ q.2 ∧
          (x q.1 = x q.2 ∨ y q.1 = y q.2))).card * B * p ^ N := by
  classical
  let C : Finset (Edge × Edge) :=
    (T.product A).filter (fun q ↦
      q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2))
  let Coll : Ω → Finset (Edge × Edge) := fun ω ↦
    (((T.filter (fun a ↦ a ∈ E ω)).product (E ω)).filter
      (fun q ↦ q.1 ≠ q.2 ∧
        (x q.1 = x q.2 ∨ y q.1 = y q.2)))
  have hColl (ω : Ω) :
      Coll ω = C.filter (fun q ↦ q.1 ∈ E ω ∧ q.2 ∈ E ω) := by
    ext q
    constructor
    · intro hq
      have hlocal := Finset.mem_filter.mp hq
      have hprod := Finset.mem_product.mp hlocal.1
      have htarget := Finset.mem_filter.mp hprod.1
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_filter.mpr ⟨
          Finset.mem_product.mpr ⟨htarget.1, hE ω hprod.2⟩,
          hlocal.2⟩,
        htarget.2, hprod.2⟩
    · intro hq
      have houter := Finset.mem_filter.mp hq
      have hglobal := Finset.mem_filter.mp houter.1
      have hprod := Finset.mem_product.mp hglobal.1
      exact Finset.mem_filter.mpr ⟨
        Finset.mem_product.mpr ⟨
          Finset.mem_filter.mpr ⟨hprod.1, houter.2.1⟩,
          houter.2.2⟩,
        hglobal.2⟩
  constructor
  · calc
      (∑ ω, (T.filter (fun a ↦ a ∈ E ω)).card) =
          ∑ a ∈ T, (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card := by
            simpa using mme_finset_incidence_double_count
              (Finset.univ : Finset Ω) T (fun ω a ↦ a ∈ E ω)
      _ = ∑ _a ∈ T, B * p ^ (N + 1) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hsingle a ha
      _ = T.card * B * p ^ (N + 1) := by simp [mul_assoc]
  · change (∑ ω, (Coll ω).card) ≤ C.card * B * p ^ N
    calc
      (∑ ω, (Coll ω).card) =
          ∑ ω, (C.filter (fun q ↦ q.1 ∈ E ω ∧ q.2 ∈ E ω)).card := by
            apply Finset.sum_congr rfl
            intro ω hω
            exact congrArg Finset.card (hColl ω)
      _ = ∑ q ∈ C,
          (Finset.univ.filter (fun ω : Ω ↦
            q.1 ∈ E ω ∧ q.2 ∈ E ω)).card := by
            simpa using mme_finset_incidence_double_count
              (Finset.univ : Finset Ω) C
                (fun ω q ↦ q.1 ∈ E ω ∧ q.2 ∈ E ω)
      _ ≤ ∑ _q ∈ C, B * p ^ N := by
        apply Finset.sum_le_sum
        intro q hq
        exact hpair q hq
      _ = C.card * B * p ^ N := by simp [mul_assoc]

private theorem mme_dwz_asymmetric_hash_retained_induced_family_of_incidence
    {Ω Edge X Y : Type}
    [Fintype Ω] [Nonempty Ω]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (E : Ω → Finset Edge)
    (N p B d : ℕ) (hp : 0 < p) (hmod : 4 * d ≤ p)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d)
    (hstateCard : Fintype.card Ω = p ^ (N + 3))
    (htarget :
      (∑ ω, (T.filter (fun a ↦ a ∈ E ω)).card) =
        T.card * B * p ^ (N + 1))
    (hcollision :
      (∑ ω, (((T.filter (fun a ↦ a ∈ E ω)).product (E ω)).filter
        (fun q ↦ q.1 ≠ q.2 ∧
          (x q.1 = x q.2 ∨ y q.1 = y q.2))).card) ≤
        (((T.product A).filter (fun q ↦ q.1 ≠ q.2 ∧
          (x q.1 = x q.2 ∨ y q.1 = y q.2))).card * B * p ^ N)) :
    ∃ ω : Ω, ∃ I : Finset Edge,
      I ⊆ T ∧
      I ⊆ E ω ∧
      (∀ e ∈ I, ∀ e' ∈ E ω,
        x e = x e' ∨ y e = y e' → e = e') ∧
      ((T.card : ℝ) * (B : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  classical
  let Target : Ω → Finset Edge := fun ω ↦ T.filter (fun a ↦ a ∈ E ω)
  let Coll : Ω → Finset (Edge × Edge) := fun ω ↦
    ((Target ω).product (E ω)).filter (fun q ↦
      q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2))
  let C : Finset (Edge × Edge) :=
    (T.product A).filter (fun q ↦
      q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2))
  let L : ℝ := ((T.card : ℝ) * (B : ℝ)) /
    (2 * (p : ℝ) ^ 2)
  have hC : C.card ≤ 2 * T.card * d := by
    exact mme_dwz_target_two_mode_collision_card_le_of_degree
      A T x y d hx hy
  have hCscaled : C.card * B * p ^ N ≤
      (2 * T.card * d * B) * p ^ N := by
    gcongr
  have hCscaledR :
      ((C.card * B * p ^ N : ℕ) : ℝ) ≤
        (((2 * T.card * d * B) * p ^ N : ℕ) : ℝ) := by
    exact_mod_cast hCscaled
  have hnormalized :=
    mme_dwz_asymmetric_hash_normalized_half_budget
      N p T.card B d hp hmod
  have hnumeric :
      (p : ℝ) ^ (N + 3) * L +
          ((C.card * B * p ^ N : ℕ) : ℝ) ≤
        ((T.card * B * p ^ (N + 1) : ℕ) : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hnormalized
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] at hCscaledR
    norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    dsimp only [L]
    linarith
  have hcollisionR :
      (∑ ω, ((Coll ω).card : ℝ)) ≤
        ((C.card * B * p ^ N : ℕ) : ℝ) := by
    exact_mod_cast hcollision
  have htargetR :
      (∑ ω, ((Target ω).card : ℝ)) =
        ((T.card * B * p ^ (N + 1) : ℕ) : ℝ) := by
    exact_mod_cast htarget
  have hstateCardR : (Fintype.card Ω : ℝ) = (p : ℝ) ^ (N + 3) := by
    exact_mod_cast hstateCard
  have havgBudget :
      (Fintype.card Ω : ℝ) * L +
          ∑ ω, ((Coll ω).card : ℝ) ≤
        ∑ ω, ((Target ω).card : ℝ) := by
    rw [hstateCardR, htargetR]
    linarith
  obtain ⟨ω, hsurplus⟩ :=
    mme_finite_collision_budget_averaging_real
      (fun ω ↦ (Target ω).card) (fun ω ↦ (Coll ω).card) L
      havgBudget
  have hTargetE : Target ω ⊆ E ω := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  obtain ⟨I, hITarget, hIE, hisolated, hcard⟩ :=
    mme_dwz_target_two_mode_isolation_pruning
      (E ω) (Target ω) hTargetE x y
  refine ⟨ω, I, ?_, ?_, hisolated, ?_⟩
  · intro a ha
    exact (Finset.mem_filter.mp (hITarget ha)).1
  · exact hIE
  · have hcardR : ((Target ω).card : ℝ) ≤
        (I.card : ℝ) + (Coll ω).card := by
      exact_mod_cast hcard
    dsimp only [L] at hsurplus ⊢
    linarith

theorem solution
    {Ω Edge X Y : Type}
    [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [DecidableEq Edge] [DecidableEq X] [DecidableEq Y]
    (A T : Finset Edge) (x : Edge → X) (y : Edge → Y)
    (E : Ω → Finset Edge)
    (N p B d : ℕ) (hp : 0 < p) (hmod : 4 * d ≤ p)
    (hE : ∀ ω, E ω ⊆ A)
    (hx : ∀ a ∈ T, (A.filter (fun b ↦ x b = x a)).card ≤ d)
    (hy : ∀ a ∈ T, (A.filter (fun b ↦ y b = y a)).card ≤ d)
    (hstateCard : Fintype.card Ω = p ^ (N + 3))
    (hsingle : ∀ a ∈ T,
      (Finset.univ.filter (fun ω : Ω ↦ a ∈ E ω)).card =
        B * p ^ (N + 1))
    (hpair : ∀ q ∈ (T.product A).filter (fun q ↦
        q.1 ≠ q.2 ∧ (x q.1 = x q.2 ∨ y q.1 = y q.2)),
      (Finset.univ.filter (fun ω : Ω ↦
        q.1 ∈ E ω ∧ q.2 ∈ E ω)).card ≤
          B * p ^ N) :
    ∃ ω : Ω, ∃ I : Finset Edge,
      I ⊆ T ∧
      I ⊆ E ω ∧
      (∀ e ∈ I, ∀ e' ∈ E ω,
        x e = x e' ∨ y e = y e' → e = e') ∧
      ((T.card : ℝ) * (B : ℝ)) /
          (2 * (p : ℝ) ^ 2) ≤ (I.card : ℝ) := by
  obtain ⟨htarget, hcollision⟩ :=
    mme_dwz_asymmetric_hash_exact_incidence_sums
      A T x y E N p B hE hsingle hpair
  exact mme_dwz_asymmetric_hash_retained_induced_family_of_incidence
    A T x y E N p B d hp hmod hx hy hstateCard htarget hcollision
