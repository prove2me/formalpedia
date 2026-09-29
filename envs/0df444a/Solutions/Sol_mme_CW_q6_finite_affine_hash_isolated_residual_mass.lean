-- Prove2me | solution 1 for mme_CW_q6_finite_affine_hash_isolated_residual_mass
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:42:50.691435+00:00
-- url     : https://prove2.me/submissions/100e5986-7fd9-44c3-8f82-294f5b18d5d0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_finite_affine_hash_raw_collision_budget
import Theorems.Thm_mme_finset_prune_two_mode_collisions_isolated

open MME

/-- Pay the explicit ordered X/Y collision budget, apply two-mode ambient
isolation, and cancel the paid collision term from the raw mass bound. -/
theorem solution :
    ∃ d : ℕ, 0 < d ∧
      ∀ (N L G : ℕ),
        CWQ6ExactAddressRegularity N L G →
        (0 < L ∧ L + G = N ∧ 341 * L < 100 * G) →
        let Zcount : ℕ :=
          Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
        let Xcount : ℕ := Nat.choose N G
        let middle : ℕ := Nat.choose (2 * G) G
        let Mmod : ℕ := 4 * Xcount ^ 2 + 1
        ∀ S : Finset ℕ,
          S ⊆ Finset.range (Mmod / 2) →
          ThreeAPFree (S : Set ℕ) →
          0 < S.card →
          ∃ E I : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              I ⊆ E ∧
              (∀ e ∈ I, ∀ e' ∈ E,
                (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
              (∀ c ∈ I.image (fun e => e.1 2),
                (I.filter (fun e => e.1 2 = c)).card ≤ middle) ∧
              (∀ ex ∈ I, ∀ ey ∈ I, ∀ ez ∈ I,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) ∧
              (H : ℝ) *
                    ((I.image (fun e => e.1 2)).card : ℝ) +
                  (middle : ℝ) *
                    ((Zcount : ℝ) *
                      ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                        (((N + 1 : ℕ) : ℝ) ^ d))) ≤
                (I.card : ℝ) := by
  classical
  obtain ⟨d, hd, hraw⟩ :=
    mme_CW_q6_finite_affine_hash_raw_collision_budget
  refine ⟨d, hd, ?_⟩
  intro N L G hregular hprofile
  dsimp only
  intro S hSrange hSfree hSpos
  obtain ⟨E, H, hH, himageE, hmaxE, hclosedE,
      hHupper, hmiddle, hmassE⟩ :=
    hraw N L G hregular hprofile S hSrange hSfree hSpos
  obtain ⟨I, hIE, hisolated, hprune⟩ :=
    mme_finset_prune_two_mode_collisions_isolated
      E (fun e => e.1 0) (fun e => e.1 1)
  have himageIE : I.image (fun e => e.1 2) ⊆
      E.image (fun e => e.1 2) := by
    intro c hc
    obtain ⟨e, heI, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_image_of_mem _ (hIE heI)
  have himageI : (I.image (fun e => e.1 2)).card ≤
      Nat.choose (2 * N) L * Nat.choose (2 * N - L) L :=
    (Finset.card_le_card himageIE).trans himageE
  have hmaxI : ∀ c ∈ I.image (fun e => e.1 2),
      (I.filter (fun e => e.1 2 = c)).card ≤ Nat.choose (2 * G) G := by
    intro c hc
    have hcE := himageIE hc
    have hfiber : I.filter (fun e => e.1 2 = c) ⊆
        E.filter (fun e => e.1 2 = c) := by
      intro e he
      exact Finset.mem_filter.mpr
        ⟨hIE (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩
    exact (Finset.card_le_card hfiber).trans (hmaxE c hcE)
  have hclosedI : ∀ ex ∈ I, ∀ ey ∈ I, ∀ ez ∈ I,
      CWQ6CoupledCoordinatewiseSupported
          (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
        ∃ e' ∈ E,
          e'.1 0 = ex.1 0 ∧
          e'.1 1 = ey.1 1 ∧
          e'.1 2 = ez.1 2 := by
    intro ex hex ey hey ez hez hsupp
    exact hclosedE ex (hIE hex) ey (hIE hey) ez (hIE hez) hsupp
  let C : Finset
      (CWQ6ExactCoupledAddress N L G × CWQ6ExactCoupledAddress N L G) :=
    (E.product E).filter (fun p =>
      p.1 ≠ p.2 ∧
        (p.1.1 0 = p.2.1 0 ∨ p.1.1 1 = p.2.1 1))
  have hpruneR : (E.card : ℝ) ≤ (I.card : ℝ) + (C.card : ℝ) := by
    exact_mod_cast hprune
  have hmassWithC := hmassE.trans hpruneR
  have hmassNoC :
      (H : ℝ) *
            (Nat.choose (2 * N) L *
              Nat.choose (2 * N - L) L : ℕ) +
          (Nat.choose (2 * G) G : ℝ) *
            (((Nat.choose (2 * N) L *
                Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              ((((S.card : ℝ) /
                  (4 * (Nat.choose N G) ^ 2 + 1 : ℕ)) ^ d) /
                (((N + 1 : ℕ) : ℝ) ^ d))) ≤
        (I.card : ℝ) := by
    exact (add_le_add_iff_right (C.card : ℝ)).mp hmassWithC
  have hfirst :
      (H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ) ≤
        (H : ℝ) *
          ((Nat.choose (2 * N) L *
            Nat.choose (2 * N - L) L : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_left
    · exact_mod_cast himageI
    · positivity
  have hmassI :
      (H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ) +
          (Nat.choose (2 * G) G : ℝ) *
            (((Nat.choose (2 * N) L *
                Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              ((((S.card : ℝ) /
                  (4 * (Nat.choose N G) ^ 2 + 1 : ℕ)) ^ d) /
                (((N + 1 : ℕ) : ℝ) ^ d))) ≤
        (I.card : ℝ) :=
    (add_le_add hfirst (le_refl _)).trans hmassNoC
  exact ⟨E, I, H, hH, hIE, hisolated, hmaxI, hclosedI,
    hHupper, hmiddle, hmassI⟩
