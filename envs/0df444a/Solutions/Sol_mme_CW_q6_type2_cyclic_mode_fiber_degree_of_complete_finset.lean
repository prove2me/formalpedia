-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_mode_fiber_degree_of_complete_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:56:53.135336+00:00
-- url     : https://prove2.me/submissions/b13417dd-4a96-4abf-9c82-6cd28478b33b

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_data
import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity

open MME

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

private theorem exactSubtypeFiberCard
    (N L G : ℕ)
    [DecidableEq (CWQ6ExactCoupledAddress N L G)]
    (A : Finset (CWQ6ExactCoupledAddress N L G))
    (hA : ∀ a, a ∈ A)
    (i : Fin 3) (w : Fin (2 * N) → Fin 3) :
    (A.filter
        (fun e ↦ e.1 i = w)).card =
      ((cwQ6ExactAddresses N L G).filter (fun e ↦ e i = w)).card := by
  classical
  apply Finset.card_bij (fun e _ ↦ e.1)
  · intro e he
    simp only [Finset.mem_filter] at he ⊢
    refine ⟨?_, he.2⟩
    simp only [cwQ6ExactAddresses, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact e.2
  · intro e _ f _ hef
    exact Subtype.ext hef
  · intro a ha
    simp only [Finset.mem_filter] at ha
    have haExact :
        CWQ6CoupledCoordinatewiseSupported a ∧
          ∀ i r : Fin 3,
            (Finset.univ.filter
              (fun j : Fin (2 * N) ↦ a i j = r)).card =
              cwQ6CoupledMarginalMultiplicity N L G i r := by
      simpa only [cwQ6ExactAddresses, Finset.mem_filter,
        Finset.mem_univ, true_and] using ha.1
    let e : CWQ6ExactCoupledAddress N L G := ⟨a, haExact⟩
    refine ⟨e, ?_, rfl⟩
    simp only [Finset.mem_filter]
    exact ⟨hA e, ha.2⟩

theorem solution
    (N L G : ℕ) (hLG : L + G = N)
    [DecidableEq (CWQ6ExactCoupledAddress N L G)]
    [DecidableEq (CWQ6Type2CyclicModeWord N)]
    (A : Finset (CWQ6ExactCoupledAddress N L G))
    (hA : ∀ a, a ∈ A)
    (e : CWQ6Type2CyclicEdge N L G) (i : Fin 3) :
    ((A ×ˢ (A ×ˢ A)).filter
      (fun f ↦ cwQ6Type2CyclicModeWord f i =
        cwQ6Type2CyclicModeWord e i)).card =
      Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
  classical
  have hregular := mme_CW_q6_exact_coupled_address_regularity N L G hLG
  have hA3 : ∀ f : CWQ6Type2CyclicEdge N L G,
      f ∈ A ×ˢ (A ×ˢ A) := by
    rintro ⟨a, b, c⟩
    exact Finset.mem_product.mpr
      ⟨hA a, Finset.mem_product.mpr ⟨hA b, hA c⟩⟩
  fin_cases i
  · change ((A ×ˢ (A ×ˢ A)).filter
        (fun f ↦ cwQ6Type2CyclicModeWord f 0 =
          cwQ6Type2CyclicModeWord e 0)).card = _
    let FX := A.filter
        (fun a ↦ a.1 0 = e.1.1 0)
    let FZ := A.filter
        (fun a ↦ a.1 2 = e.2.1.1 2)
    let FY := A.filter
        (fun a ↦ a.1 1 = e.2.2.1 1)
    have hset :
        (A ×ˢ (A ×ˢ A)).filter
            (fun f ↦ cwQ6Type2CyclicModeWord f 0 =
              cwQ6Type2CyclicModeWord e 0) =
          FX ×ˢ (FZ ×ˢ FY) := by
      ext f
      rcases f with ⟨fX, fZ, fY⟩
      constructor
      · intro hmem
        have hw := (Finset.mem_filter.mp hmem).2
        have hX : fX.1 0 = e.1.1 0 := congrArg Prod.fst hw
        have hZ : fZ.1 2 = e.2.1.1 2 :=
          congrArg Prod.fst (congrArg Prod.snd hw)
        have hY : fY.1 1 = e.2.2.1 1 :=
          congrArg Prod.snd (congrArg Prod.snd hw)
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_filter.mpr ⟨hA fX, hX⟩
        · apply Finset.mem_product.mpr
          constructor
          · exact Finset.mem_filter.mpr ⟨hA fZ, hZ⟩
          · exact Finset.mem_filter.mpr ⟨hA fY, hY⟩
      · intro h
        obtain ⟨hXmem, hrest⟩ := Finset.mem_product.mp h
        obtain ⟨hZmem, hYmem⟩ := Finset.mem_product.mp hrest
        have hX : fX.1 0 = e.1.1 0 := (Finset.mem_filter.mp hXmem).2
        have hZ : fZ.1 2 = e.2.1.1 2 := (Finset.mem_filter.mp hZmem).2
        have hY : fY.1 1 = e.2.2.1 1 := (Finset.mem_filter.mp hYmem).2
        exact Finset.mem_filter.mpr
          ⟨hA3 (fX, fZ, fY), Prod.ext hX (Prod.ext hZ hY)⟩
    rw [hset]
    have hFX : FX.card = Nat.choose N G ^ (2 : ℕ) := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.x_degree _ (Finset.mem_image.mpr ⟨e.1.1, by
        simp [cwQ6ExactAddresses, e.1.2], rfl⟩)
    have hFZ : FZ.card = Nat.choose (2 * G) G := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.z_degree _ (Finset.mem_image.mpr ⟨e.2.1.1, by
        simp [cwQ6ExactAddresses, e.2.1.2], rfl⟩)
    have hFY : FY.card = Nat.choose N G ^ (2 : ℕ) := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.y_degree _ (Finset.mem_image.mpr ⟨e.2.2.1, by
        simp [cwQ6ExactAddresses, e.2.2.2], rfl⟩)
    calc
      (FX ×ˢ (FZ ×ˢ FY)).card =
          FX.card * (FZ.card * FY.card) := by
        calc
          (FX ×ˢ (FZ ×ˢ FY)).card = FX.card * (FZ ×ˢ FY).card :=
            Finset.card_product FX (FZ ×ˢ FY)
          _ = FX.card * (FZ.card * FY.card) := by
            rw [Finset.card_product FZ FY]
      _ = Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
        rw [hFX, hFZ, hFY]
        ring
  · change ((A ×ˢ (A ×ˢ A)).filter
        (fun f ↦ cwQ6Type2CyclicModeWord f 1 =
          cwQ6Type2CyclicModeWord e 1)).card = _
    let FY := A.filter
        (fun a ↦ a.1 1 = e.1.1 1)
    let FX := A.filter
        (fun a ↦ a.1 0 = e.2.1.1 0)
    let FZ := A.filter
        (fun a ↦ a.1 2 = e.2.2.1 2)
    have hset :
        (A ×ˢ (A ×ˢ A)).filter
            (fun f ↦ cwQ6Type2CyclicModeWord f 1 =
              cwQ6Type2CyclicModeWord e 1) =
          FY ×ˢ (FX ×ˢ FZ) := by
      ext f
      rcases f with ⟨fY, fX, fZ⟩
      constructor
      · intro hmem
        have hw := (Finset.mem_filter.mp hmem).2
        have hY : fY.1 1 = e.1.1 1 := congrArg Prod.fst hw
        have hX : fX.1 0 = e.2.1.1 0 :=
          congrArg Prod.fst (congrArg Prod.snd hw)
        have hZ : fZ.1 2 = e.2.2.1 2 :=
          congrArg Prod.snd (congrArg Prod.snd hw)
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_filter.mpr ⟨hA fY, hY⟩
        · apply Finset.mem_product.mpr
          constructor
          · exact Finset.mem_filter.mpr ⟨hA fX, hX⟩
          · exact Finset.mem_filter.mpr ⟨hA fZ, hZ⟩
      · intro h
        obtain ⟨hYmem, hrest⟩ := Finset.mem_product.mp h
        obtain ⟨hXmem, hZmem⟩ := Finset.mem_product.mp hrest
        have hY : fY.1 1 = e.1.1 1 := (Finset.mem_filter.mp hYmem).2
        have hX : fX.1 0 = e.2.1.1 0 := (Finset.mem_filter.mp hXmem).2
        have hZ : fZ.1 2 = e.2.2.1 2 := (Finset.mem_filter.mp hZmem).2
        exact Finset.mem_filter.mpr
          ⟨hA3 (fY, fX, fZ), Prod.ext hY (Prod.ext hX hZ)⟩
    rw [hset]
    have hFY : FY.card = Nat.choose N G ^ (2 : ℕ) := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.y_degree _ (Finset.mem_image.mpr ⟨e.1.1, by
        simp [cwQ6ExactAddresses, e.1.2], rfl⟩)
    have hFX : FX.card = Nat.choose N G ^ (2 : ℕ) := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.x_degree _ (Finset.mem_image.mpr ⟨e.2.1.1, by
        simp [cwQ6ExactAddresses, e.2.1.2], rfl⟩)
    have hFZ : FZ.card = Nat.choose (2 * G) G := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.z_degree _ (Finset.mem_image.mpr ⟨e.2.2.1, by
        simp [cwQ6ExactAddresses, e.2.2.2], rfl⟩)
    calc
      (FY ×ˢ (FX ×ˢ FZ)).card =
          FY.card * (FX.card * FZ.card) := by
        calc
          (FY ×ˢ (FX ×ˢ FZ)).card = FY.card * (FX ×ˢ FZ).card :=
            Finset.card_product FY (FX ×ˢ FZ)
          _ = FY.card * (FX.card * FZ.card) := by
            rw [Finset.card_product FX FZ]
      _ = Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
        rw [hFY, hFX, hFZ]
        ring
  · change ((A ×ˢ (A ×ˢ A)).filter
        (fun f ↦ cwQ6Type2CyclicModeWord f 2 =
          cwQ6Type2CyclicModeWord e 2)).card = _
    let FZ := A.filter
        (fun a ↦ a.1 2 = e.1.1 2)
    let FY := A.filter
        (fun a ↦ a.1 1 = e.2.1.1 1)
    let FX := A.filter
        (fun a ↦ a.1 0 = e.2.2.1 0)
    have hset :
        (A ×ˢ (A ×ˢ A)).filter
            (fun f ↦ cwQ6Type2CyclicModeWord f 2 =
              cwQ6Type2CyclicModeWord e 2) =
          FZ ×ˢ (FY ×ˢ FX) := by
      ext f
      rcases f with ⟨fZ, fY, fX⟩
      constructor
      · intro hmem
        have hw := (Finset.mem_filter.mp hmem).2
        have hZ : fZ.1 2 = e.1.1 2 := congrArg Prod.fst hw
        have hY : fY.1 1 = e.2.1.1 1 :=
          congrArg Prod.fst (congrArg Prod.snd hw)
        have hX : fX.1 0 = e.2.2.1 0 :=
          congrArg Prod.snd (congrArg Prod.snd hw)
        apply Finset.mem_product.mpr
        constructor
        · exact Finset.mem_filter.mpr ⟨hA fZ, hZ⟩
        · apply Finset.mem_product.mpr
          constructor
          · exact Finset.mem_filter.mpr ⟨hA fY, hY⟩
          · exact Finset.mem_filter.mpr ⟨hA fX, hX⟩
      · intro h
        obtain ⟨hZmem, hrest⟩ := Finset.mem_product.mp h
        obtain ⟨hYmem, hXmem⟩ := Finset.mem_product.mp hrest
        have hZ : fZ.1 2 = e.1.1 2 := (Finset.mem_filter.mp hZmem).2
        have hY : fY.1 1 = e.2.1.1 1 := (Finset.mem_filter.mp hYmem).2
        have hX : fX.1 0 = e.2.2.1 0 := (Finset.mem_filter.mp hXmem).2
        exact Finset.mem_filter.mpr
          ⟨hA3 (fZ, fY, fX), Prod.ext hZ (Prod.ext hY hX)⟩
    rw [hset]
    have hFZ : FZ.card = Nat.choose (2 * G) G := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.z_degree _ (Finset.mem_image.mpr ⟨e.1.1, by
        simp [cwQ6ExactAddresses, e.1.2], rfl⟩)
    have hFY : FY.card = Nat.choose N G ^ (2 : ℕ) := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.y_degree _ (Finset.mem_image.mpr ⟨e.2.1.1, by
        simp [cwQ6ExactAddresses, e.2.1.2], rfl⟩)
    have hFX : FX.card = Nat.choose N G ^ (2 : ℕ) := by
      rw [exactSubtypeFiberCard N L G A hA]
      exact hregular.x_degree _ (Finset.mem_image.mpr ⟨e.2.2.1, by
        simp [cwQ6ExactAddresses, e.2.2.2], rfl⟩)
    calc
      (FZ ×ˢ (FY ×ˢ FX)).card =
          FZ.card * (FY.card * FX.card) := by
        calc
          (FZ ×ˢ (FY ×ˢ FX)).card = FZ.card * (FY ×ˢ FX).card :=
            Finset.card_product FZ (FY ×ˢ FX)
          _ = FZ.card * (FY.card * FX.card) := by
            rw [Finset.card_product FY FX]
      _ = Nat.choose N G ^ (4 : ℕ) * Nat.choose (2 * G) G := by
        rw [hFZ, hFY, hFX]
        ring
