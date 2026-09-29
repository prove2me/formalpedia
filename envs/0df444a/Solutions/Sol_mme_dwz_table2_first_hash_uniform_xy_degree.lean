-- Prove2me | solution 1 for mme_dwz_table2_first_hash_uniform_xy_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T21:01:47.19944+00:00
-- url     : https://prove2.me/submissions/99c1b082-3352-46e5-9f45-2fca1a613ddb

import Theorems.Thm_mme_dwz_table2_matchable_outer_family_component_words
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

private theorem card_composite_fiber
    {α β ι : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (g : α → β) (q : β → ι) (i : ι) :
    Fintype.card {a : α // q (g a) = i} =
      ∑ b : {b : β // q b = i},
        Fintype.card {a : α // g a = b.1} := by
  classical
  let e : {a : α // q (g a) = i} ≃
      Σ b : {b : β // q b = i}, {a : α // g a = b.1} := {
    toFun a := ⟨⟨g a.1, a.2⟩, ⟨a.1, rfl⟩⟩
    invFun a := ⟨a.2.1, by rw [a.2.2, a.1.2]⟩
    left_inv a := by
      apply Subtype.ext
      rfl
    right_inv a := by
      rcases a with ⟨⟨b, hb⟩, ⟨a, ha⟩⟩
      cases ha
      rfl
  }
  rw [Fintype.card_congr e, Fintype.card_sigma]

private theorem precomp_fiber_card
    {ι σ κ : Type*} [Fintype ι] [DecidableEq ι]
    [DecidableEq κ]
    (e : ι ≃ ι) (w : ι → σ) (q : σ → κ) (a : κ) :
    Fintype.card {t : ι // q (w (e t)) = a} =
      Fintype.card {t : ι // q (w t) = a} := by
  exact Fintype.card_congr
    (Equiv.subtypeEquiv e (fun _ => Iff.rfl))

private theorem component_xy_pushforward (r : Fin 5) :
    (∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = r},
        MME.DWZTable2Counts.component s.1) =
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = r},
        MME.DWZTable2Counts.component s.1 := by
  fin_cases r <;> decide

private theorem prescribed_fiber_nat_card
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (k : ι → ℕ) (hsum : ∑ i, k i = Fintype.card α) :
    Nat.card
        {g : α → ι // ∀ i,
          Fintype.card {a // g a = i} = k i} =
      (Fintype.card α).factorial / ∏ i, (k i).factorial := by
  rw [Nat.card_eq_fintype_card]
  exact mme_fintype_prescribed_fiber_function_card k hsum

theorem solution (m : ℕ) :
    let sourceLength := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let XWord :=
      {I : Fin sourceLength → Fin 5 //
        ∀ x, Fintype.card {t // I t = x} = alphaX x}
    let YWord :=
      {J : Fin sourceLength → Fin 5 //
        ∀ y, Fintype.card {t // J t = y} = alphaY y}
    let MarginalTriple :=
      {w : Fin sourceLength → Fin 15 //
        (∀ x, Fintype.card
            {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
        (∀ y, Fintype.card
            {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
        ∀ z, Fintype.card
            {t // MME.DWZSquare.shapeZ (w t) = z} =
              MME.DWZTable2Counts.alphaZ z * m}
    let xWord : MarginalTriple → XWord := fun w ↦
      ⟨fun t ↦ MME.DWZSquare.shapeX (w.1 t), w.2.1⟩
    let yWord : MarginalTriple → YWord := fun w ↦
      ⟨fun t ↦ MME.DWZSquare.shapeY (w.1 t), w.2.2.1⟩
    let FixedX : XWord → Type := fun I ↦
      {w : MarginalTriple // xWord w = I}
    let FixedY : YWord → Type := fun J ↦
      {w : MarginalTriple // yWord w = J}
    ∃ d : ℕ,
      Nonempty XWord ∧
      Nonempty YWord ∧
      Nonempty MarginalTriple ∧
      0 < d ∧
      (∀ I : XWord, Nat.card (FixedX I) = d) ∧
      (∀ J : YWord, Nat.card (FixedY J) = d) ∧
      Nat.card MarginalTriple = Nat.card XWord * d ∧
      Nat.card MarginalTriple = Nat.card YWord * d ∧
      Nat.card XWord = Nat.multinomial Finset.univ alphaX ∧
      Nat.card YWord = Nat.multinomial Finset.univ alphaY ∧
      Nat.card XWord = Nat.card YWord ∧
      (∀ I : XWord, 4 * Nat.card (FixedX I) ≤ 8 * d) ∧
      ∀ J : YWord, 4 * Nat.card (FixedY J) ≤ 8 * d := by
  classical
  dsimp only
  let sourceLength := MME.DWZTable2Counts.scale * m
  let alphaX : Fin 5 → ℕ := fun x ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
      MME.DWZTable2Counts.component s.1 * m
  let alphaY : Fin 5 → ℕ := fun y ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
      MME.DWZTable2Counts.component s.1 * m
  let XWord :=
    {I : Fin sourceLength → Fin 5 //
      ∀ x, Fintype.card {t // I t = x} = alphaX x}
  let YWord :=
    {J : Fin sourceLength → Fin 5 //
      ∀ y, Fintype.card {t // J t = y} = alphaY y}
  let MarginalTriple :=
    {w : Fin sourceLength → Fin 15 //
      (∀ x, Fintype.card
          {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card
          {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card
          {t // MME.DWZSquare.shapeZ (w t) = z} =
            MME.DWZTable2Counts.alphaZ z * m}
  let xWord : MarginalTriple → XWord := fun w ↦
    ⟨fun t ↦ MME.DWZSquare.shapeX (w.1 t), w.2.1⟩
  let yWord : MarginalTriple → YWord := fun w ↦
    ⟨fun t ↦ MME.DWZSquare.shapeY (w.1 t), w.2.2.1⟩
  let FixedX : XWord → Type := fun I ↦
    {w : MarginalTriple // xWord w = I}
  let FixedY : YWord → Type := fun J ↦
    {w : MarginalTriple // yWord w = J}
  change ∃ d : ℕ,
    Nonempty XWord ∧ Nonempty YWord ∧ Nonempty MarginalTriple ∧
    0 < d ∧
    (∀ I : XWord, Nat.card (FixedX I) = d) ∧
    (∀ J : YWord, Nat.card (FixedY J) = d) ∧
    Nat.card MarginalTriple = Nat.card XWord * d ∧
    Nat.card MarginalTriple = Nat.card YWord * d ∧
    Nat.card XWord = Nat.multinomial Finset.univ alphaX ∧
    Nat.card YWord = Nat.multinomial Finset.univ alphaY ∧
    Nat.card XWord = Nat.card YWord ∧
    (∀ I : XWord, 4 * Nat.card (FixedX I) ≤ 8 * d) ∧
    ∀ J : YWord, 4 * Nat.card (FixedY J) ≤ 8 * d

  obtain ⟨K, hK, hOuter, hComponent, hZ, _hInjective,
      _hOuterCard, _hOuterFactor⟩ :=
    mme_dwz_table2_matchable_outer_family_component_words m
  let Outer :=
    {w : Fin sourceLength → Fin 15 //
      (∀ t, MME.DWZSquare.shapeZ (w t) = K t) ∧
      ∀ s, Fintype.card {t // w t = s} =
        MME.DWZTable2Counts.component s * m}
  let A : Outer := Classical.choice hOuter

  have hAX (x : Fin 5) :
      Fintype.card
          {t : Fin sourceLength // MME.DWZSquare.shapeX (A.1 t) = x} =
        alphaX x := by
    rw [card_composite_fiber A.1 MME.DWZSquare.shapeX x]
    apply Finset.sum_congr rfl
    intro s hs
    exact hComponent A s.1
  have hAY (y : Fin 5) :
      Fintype.card
          {t : Fin sourceLength // MME.DWZSquare.shapeY (A.1 t) = y} =
        alphaY y := by
    rw [card_composite_fiber A.1 MME.DWZSquare.shapeY y]
    apply Finset.sum_congr rfl
    intro s hs
    exact hComponent A s.1
  have hAZ (z : Fin 5) :
      Fintype.card
          {t : Fin sourceLength // MME.DWZSquare.shapeZ (A.1 t) = z} =
        MME.DWZTable2Counts.alphaZ z * m := by
    let e :
        {t : Fin sourceLength // MME.DWZSquare.shapeZ (A.1 t) = z} ≃
          {t : Fin sourceLength // K t = z} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun t => by
        rw [hZ A t]
        simp)
    rw [Fintype.card_congr e, hK z]
  let W : MarginalTriple := ⟨A.1, hAX, hAY, hAZ⟩
  have hMarginalNonempty : Nonempty MarginalTriple := ⟨W⟩
  let I₀ : XWord := xWord W
  let J₀ : YWord := yWord W
  have hXNonempty : Nonempty XWord := ⟨I₀⟩
  have hYNonempty : Nonempty YWord := ⟨J₀⟩

  let permuteTriple (e : Fin sourceLength ≃ Fin sourceLength)
      (w : MarginalTriple) : MarginalTriple :=
    ⟨fun t ↦ w.1 (e t),
      fun x ↦ (precomp_fiber_card e w.1 MME.DWZSquare.shapeX x).trans
        (w.2.1 x),
      fun y ↦ (precomp_fiber_card e w.1 MME.DWZSquare.shapeY y).trans
        (w.2.2.1 y),
      fun z ↦ (precomp_fiber_card e w.1 MME.DWZSquare.shapeZ z).trans
        (w.2.2.2 z)⟩

  have fixedXEquiv (I J : XWord) : FixedX I ≃ FixedX J := by
    let e : Fin sourceLength ≃ Fin sourceLength :=
      Equiv.ofFiberEquiv (fun x =>
        Fintype.equivOfCardEq ((I.2 x).trans (J.2 x).symm))
    have he (t : Fin sourceLength) : J.1 (e t) = I.1 t :=
      Equiv.ofFiberEquiv_map _ t
    let toFixed (w : FixedX I) : FixedX J := by
      refine ⟨permuteTriple e.symm w.1, ?_⟩
      apply Subtype.ext
      funext t
      have hw := congrFun (congrArg Subtype.val w.2) (e.symm t)
      change MME.DWZSquare.shapeX (w.1.1 (e.symm t)) = J.1 t
      calc
        MME.DWZSquare.shapeX (w.1.1 (e.symm t)) = I.1 (e.symm t) := hw
        _ = J.1 t := by
          simpa using (he (e.symm t)).symm
    let fromFixed (w : FixedX J) : FixedX I := by
      refine ⟨permuteTriple e w.1, ?_⟩
      apply Subtype.ext
      funext t
      have hw := congrFun (congrArg Subtype.val w.2) (e t)
      change MME.DWZSquare.shapeX (w.1.1 (e t)) = I.1 t
      exact hw.trans (he t)
    exact {
      toFun := toFixed
      invFun := fromFixed
      left_inv := by
        intro w
        apply Subtype.ext
        apply Subtype.ext
        funext t
        simp only [toFixed, fromFixed, permuteTriple,
          Equiv.symm_apply_apply]
      right_inv := by
        intro w
        apply Subtype.ext
        apply Subtype.ext
        funext t
        simp only [toFixed, fromFixed, permuteTriple,
          Equiv.apply_symm_apply]
    }

  have fixedYEquiv (I J : YWord) : FixedY I ≃ FixedY J := by
    let e : Fin sourceLength ≃ Fin sourceLength :=
      Equiv.ofFiberEquiv (fun y =>
        Fintype.equivOfCardEq ((I.2 y).trans (J.2 y).symm))
    have he (t : Fin sourceLength) : J.1 (e t) = I.1 t :=
      Equiv.ofFiberEquiv_map _ t
    let toFixed (w : FixedY I) : FixedY J := by
      refine ⟨permuteTriple e.symm w.1, ?_⟩
      apply Subtype.ext
      funext t
      have hw := congrFun (congrArg Subtype.val w.2) (e.symm t)
      change MME.DWZSquare.shapeY (w.1.1 (e.symm t)) = J.1 t
      calc
        MME.DWZSquare.shapeY (w.1.1 (e.symm t)) = I.1 (e.symm t) := hw
        _ = J.1 t := by
          simpa using (he (e.symm t)).symm
    let fromFixed (w : FixedY J) : FixedY I := by
      refine ⟨permuteTriple e w.1, ?_⟩
      apply Subtype.ext
      funext t
      have hw := congrFun (congrArg Subtype.val w.2) (e t)
      change MME.DWZSquare.shapeY (w.1.1 (e t)) = I.1 t
      exact hw.trans (he t)
    exact {
      toFun := toFixed
      invFun := fromFixed
      left_inv := by
        intro w
        apply Subtype.ext
        apply Subtype.ext
        funext t
        simp only [toFixed, fromFixed, permuteTriple,
          Equiv.symm_apply_apply]
      right_inv := by
        intro w
        apply Subtype.ext
        apply Subtype.ext
        funext t
        simp only [toFixed, fromFixed, permuteTriple,
          Equiv.apply_symm_apply]
    }

  let dX := Nat.card (FixedX I₀)
  let dY := Nat.card (FixedY J₀)
  have hdX (I : XWord) : Nat.card (FixedX I) = dX := by
    exact (Nat.card_congr (fixedXEquiv I I₀)).trans rfl
  have hdY (J : YWord) : Nat.card (FixedY J) = dY := by
    exact (Nat.card_congr (fixedYEquiv J J₀)).trans rfl
  have hdXpos : 0 < dX := by
    dsimp only [dX]
    apply Finite.card_pos_iff.mpr
    exact ⟨⟨W, rfl⟩⟩

  have hFactorX :
      Nat.card MarginalTriple = Nat.card XWord * dX := by
    calc
      Nat.card MarginalTriple =
          Nat.card (Σ I : XWord, FixedX I) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv xWord)).symm
      _ = ∑ I : XWord, Nat.card (FixedX I) := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
      _ = ∑ _I : XWord, dX := by
        apply Finset.sum_congr rfl
        intro I hI
        exact hdX I
      _ = Nat.card XWord * dX := by
        simp [Nat.card_eq_fintype_card]
  have hFactorY :
      Nat.card MarginalTriple = Nat.card YWord * dY := by
    calc
      Nat.card MarginalTriple =
          Nat.card (Σ J : YWord, FixedY J) :=
        (Nat.card_congr (Equiv.sigmaFiberEquiv yWord)).symm
      _ = ∑ J : YWord, Nat.card (FixedY J) := by
        simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
      _ = ∑ _J : YWord, dY := by
        apply Finset.sum_congr rfl
        intro J hJ
        exact hdY J
      _ = Nat.card YWord * dY := by
        simp [Nat.card_eq_fintype_card]

  have hsumX : (∑ x, alphaX x) = Fintype.card (Fin sourceLength) := by
    calc
      (∑ x, alphaX x) =
          ∑ x, Fintype.card {t : Fin sourceLength // I₀.1 t = x} := by
        apply Finset.sum_congr rfl
        intro x hx
        exact (I₀.2 x).symm
      _ = Fintype.card (Σ x : Fin 5,
          {t : Fin sourceLength // I₀.1 t = x}) :=
        (Fintype.card_sigma).symm
      _ = Fintype.card (Fin sourceLength) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv I₀.1)
  have hsumY : (∑ y, alphaY y) = Fintype.card (Fin sourceLength) := by
    calc
      (∑ y, alphaY y) =
          ∑ y, Fintype.card {t : Fin sourceLength // J₀.1 t = y} := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (J₀.2 y).symm
      _ = Fintype.card (Σ y : Fin 5,
          {t : Fin sourceLength // J₀.1 t = y}) :=
        (Fintype.card_sigma).symm
      _ = Fintype.card (Fin sourceLength) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv J₀.1)
  have hXCount :
      Nat.card XWord = Nat.multinomial Finset.univ alphaX := by
    have hNat := prescribed_fiber_nat_card alphaX hsumX
    calc
      Nat.card XWord = (Fintype.card (Fin sourceLength)).factorial /
          ∏ x, (alphaX x).factorial := by
        simpa only [XWord] using hNat
      _ = Nat.multinomial Finset.univ alphaX := by
        rw [Nat.multinomial, hsumX]
  have hYCount :
      Nat.card YWord = Nat.multinomial Finset.univ alphaY := by
    have hNat := prescribed_fiber_nat_card alphaY hsumY
    calc
      Nat.card YWord = (Fintype.card (Fin sourceLength)).factorial /
          ∏ y, (alphaY y).factorial := by
        simpa only [YWord] using hNat
      _ = Nat.multinomial Finset.univ alphaY := by
        rw [Nat.multinomial, hsumY]
  have hAlphaXY : alphaX = alphaY := by
    funext r
    dsimp only [alphaX, alphaY]
    rw [← Finset.sum_mul, ← Finset.sum_mul, component_xy_pushforward r]
  have hXYCount : Nat.card XWord = Nat.card YWord := by
    rw [hXCount, hYCount, hAlphaXY]
  have hdYX : dY = dX := by
    apply Nat.eq_of_mul_eq_mul_left (show 0 < Nat.card XWord from
      Finite.card_pos_iff.mpr hXNonempty)
    calc
      Nat.card XWord * dY = Nat.card YWord * dY := by rw [hXYCount]
      _ = Nat.card MarginalTriple := hFactorY.symm
      _ = Nat.card XWord * dX := hFactorX

  refine ⟨dX, hXNonempty, hYNonempty, hMarginalNonempty, hdXpos,
    hdX, ?_, hFactorX, ?_, hXCount, hYCount, hXYCount, ?_, ?_⟩
  · intro J
    rw [hdY J, hdYX]
  · simpa only [hdYX] using hFactorY
  · intro I
    rw [hdX I]
    omega
  · intro J
    rw [hdY J, hdYX]
    omega
