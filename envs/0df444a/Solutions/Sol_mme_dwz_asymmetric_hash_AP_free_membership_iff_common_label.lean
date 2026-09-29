-- Prove2me | solution 1 for mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T05:20:40.69381+00:00
-- url     : https://prove2.me/submissions/b97c218d-173f-4621-901f-96260e45ed25

import Definitions.Def_mme_dwz_asymmetric_affine_hash
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_identity
import Theorems.Thm_mme_dwz_threeAP_free_cast_labels_collapse

set_option autoImplicit false
set_option warningAsError true

open MME

theorem solution
    {p N : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (levelSum : ZMod p) (I J K : Fin (N + 1) → ZMod p)
    (hsupport : ∀ t, I t + J t + K t = levelSum)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    let castS : Finset (ZMod p) :=
      S.image (fun a : ℕ ↦ (a : ZMod p))
    let ω := dwzAsymmetricHashStateOfAffine q
    (dwzAsymmetricHashX ω I ∈ castS ∧
        dwzAsymmetricHashY ω J ∈ castS ∧
        dwzAsymmetricHashZ levelSum ω K ∈ castS) ↔
      dwzAsymmetricAffineRetains levelSum castS I J K q := by
  classical
  dsimp only
  let ω := dwzAsymmetricHashStateOfAffine q
  constructor
  · rintro ⟨hXmem, hYmem, hZmem⟩
    obtain ⟨x, hxS, hx⟩ := Finset.mem_image.mp hXmem
    obtain ⟨y, hyS, hy⟩ := Finset.mem_image.mp hYmem
    obtain ⟨z, hzS, hz⟩ := Finset.mem_image.mp hZmem
    have hap := mme_dwz_asymmetric_hash_AP_identity
      hpodd levelSum ω I J K hsupport
    have hlabels :
        (x : ZMod p) + (y : ZMod p) = 2 * (z : ZMod p) := by
      calc
        (x : ZMod p) + (y : ZMod p) =
            dwzAsymmetricHashX ω I + dwzAsymmetricHashY ω J := by
          rw [hx, hy]
        _ = 2 * dwzAsymmetricHashZ levelSum ω K := hap
        _ = 2 * (z : ZMod p) := by rw [hz]
    obtain ⟨hxz, hzy⟩ := mme_dwz_threeAP_free_cast_labels_collapse
      p S hSrange hSfree x y z hxS hyS hzS hlabels
    refine ⟨(z : ZMod p), Finset.mem_image.mpr ⟨z, hzS, rfl⟩,
      hx.symm.trans (congrArg (fun n : ℕ ↦ (n : ZMod p)) hxz),
      hy.symm.trans
        (congrArg (fun n : ℕ ↦ (n : ZMod p)) hzy).symm,
      hz.symm⟩
  · rintro ⟨s, hs, hX, hY, hZ⟩
    exact ⟨by simpa [hX] using hs,
      by simpa [hY] using hs,
      by simpa [hZ] using hs⟩
