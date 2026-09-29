-- Prove2me | solution 1 for mme_dwz_common_state_hash_retained_of_bucket_same_z
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:55:58.588935+00:00
-- url     : https://prove2.me/submissions/a343d053-2ea8-4965-956c-9a7d0e22a0b5

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Theorems.Thm_mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label

open MME

set_option autoImplicit false
set_option warningAsError true

open MME.DWZGlobalCorrelated

/-- Two canonical-bucket owners in one coarse-Z fiber satisfy the exact
common-state X--Z hash predicate used by the correlated broken copy. -/
theorem solution
    {p N n : ℕ} (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (hBucket : ∀ j, edge j ∈ dwzTable2AffineHashBucket S A q)
    (owner competitor : Fin n)
    (hSameZ : sameCoarseZ edge owner competitor) :
    commonStateHashRetained q edge owner competitor := by
  classical
  let central := edge owner
  let candidate := edge competitor
  let ω := dwzAsymmetricHashStateOfAffine q
  have hCandidateMembership := (Finset.mem_filter.mp (hBucket competitor)).2
  have hSupport : ∀ t,
      dwzTable2CastX (p := p) candidate t +
          dwzTable2CastY candidate t + dwzTable2CastZ candidate t =
        (4 : ZMod p) := by
    intro t
    have hsum := MME.DWZSquare.shape_sum (candidate t)
    have hcast := congrArg (fun a : ℕ ↦ (a : ZMod p)) hsum
    simpa only [dwzTable2CastX, dwzTable2CastY, dwzTable2CastZ,
      Nat.cast_add, Nat.cast_ofNat] using hcast
  have hRetains :=
    (mme_dwz_asymmetric_hash_AP_free_membership_iff_common_label
      hpodd S hSrange hSfree (4 : ZMod p)
      (dwzTable2CastX candidate) (dwzTable2CastY candidate)
      (dwzTable2CastZ candidate) hSupport q).mp hCandidateMembership
  obtain ⟨s, hs, hX, hY, hZ⟩ := hRetains
  have hCastZ : dwzTable2CastZ (p := p) candidate =
      dwzTable2CastZ (p := p) central := by
    funext t
    exact congrArg (fun z : Fin 5 ↦ (z.val : ZMod p)) (hSameZ t)
  unfold commonStateHashRetained
  dsimp only [ω, central, candidate] at hX hZ hCastZ ⊢
  rw [hX, ← hZ, hCastZ]
