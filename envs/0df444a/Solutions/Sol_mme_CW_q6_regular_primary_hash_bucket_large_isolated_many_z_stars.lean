-- Prove2me | solution 1 for mme_CW_q6_regular_primary_hash_bucket_large_isolated_many_z_stars
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:33:46.968331+00:00
-- url     : https://prove2.me/submissions/82fc1d7b-ae7d-44bf-b160-ba0563ecfb0d

import Mathlib
import Theorems.Thm_mme_CW_q6_eventual_threshold_choice
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_margin_isolated_many_z_stars

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution
    {n L G : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hG : 0 < G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      (4 * (Nat.choose (n + 1) G) ^ 2 + 1))
    (hlarge :
      400 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ≤
        Nat.choose (2 * G) G) :
    ∃ w : Fin (2 * n + 2) →
          ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
      ∃ b0 : ZMod (4 * (Nat.choose (n + 1) G) ^ 2 + 1),
        ∃ I : Finset (CWQ6ExactCoupledAddress (n + 1) L G),
          I ⊆ cwQ6PrimaryHashBucket (n + 1) L G
              (Nat.choose (n + 1) G) S b0 w ∧
          (∀ e ∈ I,
            ∀ e' ∈ cwQ6PrimaryHashBucket (n + 1) L G
                (Nat.choose (n + 1) G) S b0 w,
              (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
          (S.card * (cwQ6ExactZWords (n + 1) L G).card) /
                (16 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) ≤
            ((cwQ6ExactZWords (n + 1) L G).filter (fun z =>
              Nat.choose (2 * G) G /
                    (8 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) ≤
                (I.filter (fun e => e.1 2 = z)).card)).card := by
  let X : ℕ := Nat.choose (n + 1) G
  let B : ℕ := Nat.choose (2 * G) G
  let M : ℕ := 4 * X ^ 2 + 1
  let Z : Finset (Fin (2 * (n + 1)) → Fin 3) :=
    cwQ6ExactZWords (n + 1) L G
  let K : ℕ := (3 * B) / (4 * M)
  let H : ℕ := B / (8 * M)
  let R : ℕ := B / 4
  let Q : ℕ := (S.card * Z.card) / (16 * M)
  have hM : 0 < M := by
    dsimp [M]
    omega
  have hthreshold := mme_CW_q6_eventual_threshold_choice
    (B := B) (M := M) (S := S.card) (Z := Z.card) hM
    (by simpa only [B, M, X] using hlarge)
  change 0 < R ∧ H ≤ K ∧ M * K + R ≤ B ∧
      16 * B * M ≤ R ^ 2 ∧
      5 * B ≤ 8 * M * (K - H + 1) ∧
      16 * M * Q ≤ S.card * Z.card at hthreshold
  rcases hthreshold with ⟨hR, hHK, hgap, hRmargin, hDmargin, hQmargin⟩
  have hresult :=
    mme_CW_q6_regular_primary_hash_bucket_margin_isolated_many_z_stars
      hregular hG hHK hR S
        (by simpa only [M, X] using hSrange)
        (by simpa only [M, X, B] using hgap)
        (by simpa only [M, X, B] using hRmargin)
        (by simpa only [M, X, B] using hDmargin)
        (by simpa only [M, X, Z] using hQmargin)
  simpa only [Q, H, M, B, X, Z] using hresult
