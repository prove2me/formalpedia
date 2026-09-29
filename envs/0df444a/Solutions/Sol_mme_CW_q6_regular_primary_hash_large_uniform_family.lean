-- Prove2me | solution 1 for mme_CW_q6_regular_primary_hash_large_uniform_family
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:57:42.826559+00:00
-- url     : https://prove2.me/submissions/9b820dcf-9210-4a4f-8d21-103caa950c0d

import Mathlib
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_large_isolated_many_z_stars
import Theorems.Thm_mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_structure

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem solution
    {n L G : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hG : 0 < G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      ((4 * (Nat.choose (n + 1) G) ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (hlarge :
      400 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ≤
        Nat.choose (2 * G) G) :
    ∃ A H : ℕ,
      Nonempty (CWQ6PrimaryHashFamily (n + 1) L G A H) ∧
      (S.card * (cwQ6ExactZWords (n + 1) L G).card) /
            (16 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) ≤ A ∧
      H = Nat.choose (2 * G) G /
            (8 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) := by
  classical
  let X : ℕ := Nat.choose (n + 1) G
  let B : ℕ := Nat.choose (2 * G) G
  let M : ℕ := 4 * X ^ 2 + 1
  let Z : Finset (Fin (2 * (n + 1)) → Fin 3) :=
    cwQ6ExactZWords (n + 1) L G
  let H : ℕ := B / (8 * M)
  let Q : ℕ := (S.card * Z.card) / (16 * M)
  have hM : 0 < M := by
    dsimp [M]
    omega
  have hlarge' : 400 * M ≤ B := by
    simpa only [M, X, B] using hlarge
  have hH : 0 < H := by
    dsimp only [H]
    exact Nat.div_pos (by omega) (by positivity)
  have hSrangeFull : S ⊆ Finset.range M := by
    intro s hs
    have hslt : s < M / 2 := Finset.mem_range.mp (hSrange hs)
    exact Finset.mem_range.mpr (lt_of_lt_of_le hslt (Nat.div_le_self M 2))
  obtain ⟨w, b0, I, hIE, hisolated, hQ⟩ :=
    mme_CW_q6_regular_primary_hash_bucket_large_isolated_many_z_stars
      hregular hG S
      (by simpa only [M, X] using hSrangeFull)
      (by simpa only [M, X, B] using hlarge')
  let E : Finset (CWQ6ExactCoupledAddress (n + 1) L G) :=
    cwQ6PrimaryHashBucket (n + 1) L G X S b0 w
  let Zgood : Finset (Fin (2 * (n + 1)) → Fin 3) :=
    Z.filter (fun z => H ≤ (I.filter (fun e => e.1 2 = z)).card)
  let F : Finset (CWQ6ExactCoupledAddress (n + 1) L G) :=
    I.filter (fun e => e.1 2 ∈ Zgood)
  have hIE' : I ⊆ E := by
    simpa only [E, X] using hIE
  have hFE : F ⊆ E := by
    intro e he
    exact hIE' (Finset.mem_filter.mp he).1
  have himage : F.image (fun e => e.1 2) = Zgood := by
    apply Finset.Subset.antisymm
    · intro z hz
      obtain ⟨e, heF, rfl⟩ := Finset.mem_image.mp hz
      exact (Finset.mem_filter.mp heF).2
    · intro z hz
      have hzdeg : H ≤ (I.filter (fun e => e.1 2 = z)).card :=
        (Finset.mem_filter.mp hz).2
      have hfiberPos : 0 < (I.filter (fun e => e.1 2 = z)).card :=
        lt_of_lt_of_le hH hzdeg
      obtain ⟨e, he⟩ := Finset.card_pos.mp hfiberPos
      have heI := (Finset.mem_filter.mp he).1
      have hez := (Finset.mem_filter.mp he).2
      refine Finset.mem_image.mpr ⟨e, ?_, hez⟩
      exact Finset.mem_filter.mpr ⟨heI, hez ▸ hz⟩
  have hmin : ∀ c ∈ F.image (fun e => e.1 2),
      H ≤ (F.filter (fun e => e.1 2 = c)).card := by
    intro c hc
    have hcgood : c ∈ Zgood := himage ▸ hc
    have hcdeg : H ≤ (I.filter (fun e => e.1 2 = c)).card :=
      (Finset.mem_filter.mp hcgood).2
    have hfiberEq :
        F.filter (fun e => e.1 2 = c) =
          I.filter (fun e => e.1 2 = c) := by
      ext e
      constructor
      · intro he
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1,
            (Finset.mem_filter.mp he).2⟩
      · intro he
        have heI := (Finset.mem_filter.mp he).1
        have hec := (Finset.mem_filter.mp he).2
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_filter.mpr ⟨heI, hec ▸ hcgood⟩, hec⟩
    rw [hfiberEq]
    exact hcdeg
  have hstructure := mme_CW_q6_primary_hash_bucket_structure
    (n + 1) L G X hregular S hSrange hSfree b0 w
  change
      (E.image (fun e => e.1 2)).card ≤
          Nat.choose (2 * (n + 1)) L * Nat.choose (2 * (n + 1) - L) L ∧
      (∀ c ∈ E.image (fun e => e.1 2),
        (E.filter (fun e => e.1 2 = c)).card ≤ Nat.choose (2 * G) G) ∧
      (∀ ex ∈ E, ∀ ey ∈ E, ∀ ez ∈ E,
        CWQ6CoupledCoordinatewiseSupported
            (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
          ∃ e' ∈ E,
            e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2) at hstructure
  have hclosedF : ∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
      CWQ6CoupledCoordinatewiseSupported
        (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
      ∃ e' ∈ E,
        e'.1 0 = ex.1 0 ∧ e'.1 1 = ey.1 1 ∧ e'.1 2 = ez.1 2 := by
    intro ex hex ey hey ez hez hsupp
    exact hstructure.2.2 ex (hFE hex) ey (hFE hey) ez (hFE hez) hsupp
  have hfamily := mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
    (n + 1) L G H E F hH hFE
      (fun e he e' he' hcollision =>
        hisolated e (Finset.mem_filter.mp he).1 e'
          (by simpa only [E, X] using he') hcollision)
      hmin hclosedF
  refine ⟨(F.image (fun e => e.1 2)).card, H, hfamily, ?_, rfl⟩
  rw [himage]
  simpa only [Q, H, M, B, X, Z] using hQ
