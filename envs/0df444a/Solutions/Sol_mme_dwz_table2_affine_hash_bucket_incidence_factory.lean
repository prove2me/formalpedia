-- Prove2me | solution 1 for mme_dwz_table2_affine_hash_bucket_incidence_factory
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T12:49:22.233901+00:00
-- url     : https://prove2.me/submissions/ee3c8aff-3b8f-49ff-afa4-8cda4d5b6e77

import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_dwz_asymmetric_hash_singleton_fiber_card
import Theorems.Thm_mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
import Theorems.Thm_mme_dwz_table2_component_words_affine_hash_adapter
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
import Theorems.Thm_mme_lower_half_ZMod_image_card

set_option autoImplicit false
set_option warningAsError true

open MME

/-- The public, canonical Table-2 affine bucket has exactly the one-word and
shared-X/Y pair incidences used by the first asymmetric-hash retention
argument.  Unlike the earlier existential factory, this statement preserves
the literal bucket definition needed by Claim 6.8. -/
theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp5 : 5 ≤ p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A T : Finset (Fin (N + 1) → Fin 15)) (hTA : T ⊆ A) :
    let Edge := Fin (N + 1) → Fin 15
    let XWord := Fin (N + 1) → Fin 5
    let x : Edge → XWord := fun w t ↦ DWZSquare.shapeX (w t)
    let y : Edge → XWord := fun w t ↦ DWZSquare.shapeY (w t)
    let Ω := (Fin (N + 2) → ZMod p) × ZMod p
    Fintype.card Ω = p ^ (N + 3) ∧
      (∀ q : Ω, dwzTable2AffineHashBucket S A q ⊆ A) ∧
      (∀ a ∈ T,
        (Finset.univ.filter (fun q : Ω ↦
          a ∈ dwzTable2AffineHashBucket S A q)).card =
            S.card * p ^ (N + 1)) ∧
      ∀ ab ∈ (T.product A).filter (fun ab ↦
          ab.1 ≠ ab.2 ∧ (x ab.1 = x ab.2 ∨ y ab.1 = y ab.2)),
        (Finset.univ.filter (fun q : Ω ↦
          ab.1 ∈ dwzTable2AffineHashBucket S A q ∧
            ab.2 ∈ dwzTable2AffineHashBucket S A q)).card ≤
              S.card * p ^ N := by
  classical
  dsimp only
  let castS : Finset (ZMod p) :=
    S.image (fun a : ℕ ↦ (a : ZMod p))
  have hsupport (w : Fin (N + 1) → Fin 15) (t : Fin (N + 1)) :
      dwzTable2CastX w t + dwzTable2CastY w t + dwzTable2CastZ w t =
        (4 : ZMod p) := by
    have hsum := DWZSquare.shape_sum (w t)
    have hcast := congrArg (fun n : ℕ ↦ (n : ZMod p)) hsum
    simpa only [dwzTable2CastX, dwzTable2CastY, dwzTable2CastZ,
      Nat.cast_add, Nat.cast_ofNat] using hcast
  have hcastCard : castS.card = S.card := by
    exact mme_lower_half_ZMod_image_card p S hSrange
  have hE : ∀ q : (Fin (N + 2) → ZMod p) × ZMod p,
      dwzTable2AffineHashBucket S A q ⊆ A := by
    intro q w hw
    exact (Finset.mem_filter.mp hw).1
  have hsingle : ∀ a ∈ T,
      (Finset.univ.filter (fun q :
          (Fin (N + 2) → ZMod p) × ZMod p ↦
        a ∈ dwzTable2AffineHashBucket S A q)).card =
          S.card * p ^ (N + 1) := by
    intro a haT
    have haA : a ∈ A := hTA haT
    have hsets :
        Finset.univ.filter (fun q :
            (Fin (N + 2) → ZMod p) × ZMod p ↦
          a ∈ dwzTable2AffineHashBucket S A q) =
        dwzAsymmetricAffineStatesRetaining (4 : ZMod p) castS
          (dwzTable2CastX a) (dwzTable2CastY a)
          (dwzTable2CastZ a) := by
      ext q
      simp only [dwzTable2AffineHashBucket,
        dwzAsymmetricAffineStatesRetaining, Finset.mem_filter,
        Finset.mem_univ, true_and, haA]
      exact mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
        hpodd S hSrange hSfree (4 : ZMod p)
          (dwzTable2CastX a) (dwzTable2CastY a)
          (dwzTable2CastZ a) (hsupport a) q
    rw [hsets, mme_dwz_asymmetric_hash_singleton_fiber_card
      hpodd (4 : ZMod p) castS (dwzTable2CastX a)
        (dwzTable2CastY a) (dwzTable2CastZ a) (hsupport a), hcastCard]
  have hpair : ∀ ab ∈ (T.product A).filter (fun ab ↦
      ab.1 ≠ ab.2 ∧
        ((fun t ↦ DWZSquare.shapeX (ab.1 t)) =
            (fun t ↦ DWZSquare.shapeX (ab.2 t)) ∨
          (fun t ↦ DWZSquare.shapeY (ab.1 t)) =
            (fun t ↦ DWZSquare.shapeY (ab.2 t)))),
      (Finset.univ.filter (fun q :
          (Fin (N + 2) → ZMod p) × ZMod p ↦
        ab.1 ∈ dwzTable2AffineHashBucket S A q ∧
          ab.2 ∈ dwzTable2AffineHashBucket S A q)).card ≤
            S.card * p ^ N := by
    intro ab hab
    have hab' := Finset.mem_filter.mp hab
    have hprod := Finset.mem_product.mp hab'.1
    have haT : ab.1 ∈ T := hprod.1
    have hbA : ab.2 ∈ A := hprod.2
    have haA : ab.1 ∈ A := hTA haT
    have hne : ab.1 ≠ ab.2 := hab'.2.1
    have hshare := hab'.2.2
    have hadapter := mme_dwz_table2_component_words_affine_hash_adapter
      hp5 ab.1 ab.2 hne hshare
    dsimp only at hadapter
    have hsets :
        Finset.univ.filter (fun q :
            (Fin (N + 2) → ZMod p) × ZMod p ↦
          ab.1 ∈ dwzTable2AffineHashBucket S A q ∧
            ab.2 ∈ dwzTable2AffineHashBucket S A q) =
          (dwzAsymmetricAffineStatesRetaining (4 : ZMod p) castS
              (dwzTable2CastX ab.1) (dwzTable2CastY ab.1)
              (dwzTable2CastZ ab.1)) ∩
            (dwzAsymmetricAffineStatesRetaining (4 : ZMod p) castS
              (dwzTable2CastX ab.2) (dwzTable2CastY ab.2)
              (dwzTable2CastZ ab.2)) := by
      ext q
      simp only [dwzTable2AffineHashBucket,
        dwzAsymmetricAffineStatesRetaining, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_inter, haA, hbA]
      exact and_congr
        (mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
          hpodd S hSrange hSfree (4 : ZMod p)
            (dwzTable2CastX ab.1) (dwzTable2CastY ab.1)
            (dwzTable2CastZ ab.1) hadapter.1 q)
        (mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
          hpodd S hSrange hSfree (4 : ZMod p)
            (dwzTable2CastX ab.2) (dwzTable2CastY ab.2)
            (dwzTable2CastZ ab.2) hadapter.2.1 q)
    rw [hsets]
    have hbound := mme_dwz_asymmetric_hash_shared_XY_pair_fiber_card_le
      (4 : ZMod p) castS
        (dwzTable2CastX ab.1) (dwzTable2CastY ab.1)
        (dwzTable2CastZ ab.1) (dwzTable2CastX ab.2)
        (dwzTable2CastY ab.2) (dwzTable2CastZ ab.2)
        hadapter.2.2
    simpa only [hcastCard] using hbound
  refine ⟨?_, hE, hsingle, hpair⟩
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    ZMod.card]
  ring
