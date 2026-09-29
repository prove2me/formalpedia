-- Prove2me | solution 1 for mme_dwz_table2_raw_marginal_family_uniform_xy_degree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:15:12.407086+00:00
-- url     : https://prove2.me/submissions/1f7336a4-280a-409e-8e60-baf4ae976c37

import Theorems.Thm_mme_dwz_table2_first_hash_uniform_xy_degree_rate

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

open MME

theorem solution (m : ℕ) :
    let L := MME.DWZTable2Counts.scale * m
    let alphaX : Fin 5 → ℕ := fun x ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
        MME.DWZTable2Counts.component s.1 * m
    let alphaY : Fin 5 → ℕ := fun y ↦
      ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
        MME.DWZTable2Counts.component s.1 * m
    let P : (Fin L → Fin 15) → Prop := fun w ↦
      (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
      (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
      ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
        MME.DWZTable2Counts.alphaZ z * m
    let A : Finset (Fin L → Fin 15) := Finset.univ.filter P
    ∃ d : ℕ,
      0 < d ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeX (b t)) =
            (fun t ↦ MME.DWZSquare.shapeX (a t)))).card = d) ∧
      (∀ a ∈ A,
        (A.filter (fun b ↦
          (fun t ↦ MME.DWZSquare.shapeY (b t)) =
            (fun t ↦ MME.DWZSquare.shapeY (a t)))).card = d) ∧
      (d : ℝ) ≤
        (6 * (((L + 1 : ℕ) : ℝ))) ^ 5 *
          (((L + 1 : ℕ) : ℝ)) ^ 15 *
          Real.exp
            ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
              (MME.DWZSquare.maxSameMarginalEntropy -
                mme_modern_entropyBits
                  (mme_modern_marginal MME.DWZSquare.shapeX
                    MME.DWZSquare.alpha))) := by
  classical
  dsimp only
  let L := MME.DWZTable2Counts.scale * m
  let alphaX : Fin 5 → ℕ := fun x ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeX s = x},
      MME.DWZTable2Counts.component s.1 * m
  let alphaY : Fin 5 → ℕ := fun y ↦
    ∑ s : {s : Fin 15 // MME.DWZSquare.shapeY s = y},
      MME.DWZTable2Counts.component s.1 * m
  let P : (Fin L → Fin 15) → Prop := fun w ↦
    (∀ x, Fintype.card {t // MME.DWZSquare.shapeX (w t) = x} = alphaX x) ∧
    (∀ y, Fintype.card {t // MME.DWZSquare.shapeY (w t) = y} = alphaY y) ∧
    ∀ z, Fintype.card {t // MME.DWZSquare.shapeZ (w t) = z} =
      MME.DWZTable2Counts.alphaZ z * m
  let A : Finset (Fin L → Fin 15) := Finset.univ.filter P
  let XWord :=
    {I : Fin L → Fin 5 //
      ∀ x, Fintype.card {t // I t = x} = alphaX x}
  let YWord :=
    {J : Fin L → Fin 5 //
      ∀ y, Fintype.card {t // J t = y} = alphaY y}
  let MarginalTriple := {w : Fin L → Fin 15 // P w}
  let xWord : MarginalTriple → XWord := fun w ↦
    ⟨fun t ↦ MME.DWZSquare.shapeX (w.1 t), w.2.1⟩
  let yWord : MarginalTriple → YWord := fun w ↦
    ⟨fun t ↦ MME.DWZSquare.shapeY (w.1 t), w.2.2.1⟩
  let FixedX : XWord → Type := fun I ↦
    {w : MarginalTriple // xWord w = I}
  let FixedY : YWord → Type := fun J ↦
    {w : MarginalTriple // yWord w = J}
  obtain ⟨d, _hXNonempty, _hYNonempty, _hMarginalNonempty, hd,
      hFixedX, hFixedY, _hFactorX, _hFactorY, _hXCount, _hYCount,
      _hXYCount, hrate⟩ :=
    mme_dwz_table2_first_hash_uniform_xy_degree_rate m
  refine ⟨d, hd, ?_, ?_, hrate⟩
  · intro a haA
    have haP : P a := (Finset.mem_filter.mp haA).2
    let aM : MarginalTriple := ⟨a, haP⟩
    let aX : XWord := xWord aM
    let Star := A.filter (fun b ↦
      (fun t ↦ MME.DWZSquare.shapeX (b t)) =
        (fun t ↦ MME.DWZSquare.shapeX (a t)))
    let e : (↥Star) ≃ FixedX aX := {
      toFun := fun b ↦ by
        have hb := Finset.mem_filter.mp b.2
        have hbP : P b.1 := (Finset.mem_filter.mp hb.1).2
        let bM : MarginalTriple := ⟨b.1, hbP⟩
        refine ⟨bM, ?_⟩
        apply Subtype.ext
        exact hb.2
      invFun := fun b ↦ by
        refine ⟨b.1.1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.1.2⟩
        · exact congrArg Subtype.val b.2
      left_inv := by
        intro b
        apply Subtype.ext
        rfl
      right_inv := by
        intro b
        apply Subtype.ext
        apply Subtype.ext
        rfl
    }
    change Star.card = d
    calc
      Star.card = Fintype.card (↥Star) := (Fintype.card_coe Star).symm
      _ = Fintype.card (FixedX aX) := Fintype.card_congr e
      _ = Nat.card (FixedX aX) := Nat.card_eq_fintype_card.symm
      _ = d := hFixedX aX
  · intro a haA
    have haP : P a := (Finset.mem_filter.mp haA).2
    let aM : MarginalTriple := ⟨a, haP⟩
    let aY : YWord := yWord aM
    let Star := A.filter (fun b ↦
      (fun t ↦ MME.DWZSquare.shapeY (b t)) =
        (fun t ↦ MME.DWZSquare.shapeY (a t)))
    let e : (↥Star) ≃ FixedY aY := {
      toFun := fun b ↦ by
        have hb := Finset.mem_filter.mp b.2
        have hbP : P b.1 := (Finset.mem_filter.mp hb.1).2
        let bM : MarginalTriple := ⟨b.1, hbP⟩
        refine ⟨bM, ?_⟩
        apply Subtype.ext
        exact hb.2
      invFun := fun b ↦ by
        refine ⟨b.1.1, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.1.2⟩
        · exact congrArg Subtype.val b.2
      left_inv := by
        intro b
        apply Subtype.ext
        rfl
      right_inv := by
        intro b
        apply Subtype.ext
        apply Subtype.ext
        rfl
    }
    change Star.card = d
    calc
      Star.card = Fintype.card (↥Star) := (Fintype.card_coe Star).symm
      _ = Fintype.card (FixedY aY) := Fintype.card_congr e
      _ = Nat.card (FixedY aY) := Nat.card_eq_fintype_card.symm
      _ = d := hFixedY aY
