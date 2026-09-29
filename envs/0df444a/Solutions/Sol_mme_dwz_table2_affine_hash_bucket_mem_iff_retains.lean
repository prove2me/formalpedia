-- Prove2me | solution 1 for mme_dwz_table2_affine_hash_bucket_mem_iff_retains
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T02:15:07.737725+00:00
-- url     : https://prove2.me/submissions/7712c991-4b3d-49e2-8574-76991d5cc185

import Definitions.Def_mme_dwz_table2_affine_hash_bucket
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (a : Fin (N + 1) → Fin 15) (ha : a ∈ A)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    let castS : Finset (ZMod p) :=
      S.image (fun x : ℕ ↦ (x : ZMod p))
    a ∈ MME.dwzTable2AffineHashBucket S A q ↔
      MME.dwzAsymmetricAffineRetains (4 : ZMod p) castS
        (MME.dwzTable2CastX a) (MME.dwzTable2CastY a)
        (MME.dwzTable2CastZ a) q := by
  dsimp only
  have hsupport : ∀ t,
      MME.dwzTable2CastX (p := p) a t +
          MME.dwzTable2CastY a t + MME.dwzTable2CastZ a t =
        (4 : ZMod p) := by
    intro t
    have hs := MME.DWZSquare.shape_sum (a t)
    have hc := congrArg (fun x : ℕ ↦ (x : ZMod p)) hs
    simpa only [MME.dwzTable2CastX, MME.dwzTable2CastY,
      MME.dwzTable2CastZ, Nat.cast_add, Nat.cast_ofNat] using hc
  simp only [MME.dwzTable2AffineHashBucket, Finset.mem_filter, ha,
    true_and]
  exact mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
    hpodd S hSrange hSfree (4 : ZMod p)
      (MME.dwzTable2CastX a) (MME.dwzTable2CastY a)
      (MME.dwzTable2CastZ a) hsupport q
