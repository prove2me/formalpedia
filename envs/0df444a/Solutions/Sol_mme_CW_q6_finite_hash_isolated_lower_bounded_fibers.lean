-- Prove2me | solution 1 for mme_CW_q6_finite_hash_isolated_lower_bounded_fibers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:35:26.497053+00:00
-- url     : https://prove2.me/submissions/8fdd6712-42f2-4d2a-a246-f880a432b079
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_finite_affine_hash_isolated_residual_mass
import Theorems.Thm_mme_finset_degree_threshold

open MME

/-- The residual affine-hash mass estimate, followed by deterministic fiber
thresholding, gives exactly the isolated lower-bounded family target. -/
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
          ∃ E F : Finset (CWQ6ExactCoupledAddress N L G),
            ∃ H : ℕ,
              0 < H ∧
              F ⊆ E ∧
              (∀ e ∈ F, ∀ e' ∈ E,
                (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e') ∧
              (∀ c ∈ F.image (fun e => e.1 2),
                H ≤ (F.filter (fun e => e.1 2 = c)).card) ∧
              (∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
                CWQ6CoupledCoordinatewiseSupported
                    (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
                  ∃ e' ∈ E,
                    e'.1 0 = ex.1 0 ∧
                    e'.1 1 = ey.1 1 ∧
                    e'.1 2 = ez.1 2) ∧
              H ≤ 4 ^ N ∧
              (Zcount : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                ((F.image (fun e => e.1 2)).card : ℝ) ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  classical
  obtain ⟨d, hd, hhash⟩ :=
    mme_CW_q6_finite_affine_hash_isolated_residual_mass
  refine ⟨d, hd, ?_⟩
  intro N L G hregular hprofile
  dsimp only
  intro S hSrange hSfree hSpos
  obtain ⟨E, I, H, hH, hIE, hisolated, hmax, hclosed,
      hHupper, hmiddle, hmass⟩ :=
    hhash N L G hregular hprofile S hSrange hSfree hSpos
  let F : Finset (CWQ6ExactCoupledAddress N L G) :=
    I.filter (fun e =>
      H ≤ (I.filter (fun e' => e'.1 2 = e.1 2)).card)
  have hthreshold := mme_finset_degree_threshold
    I (fun e => e.1 2) H (Nat.choose (2 * G) G) hmax
  dsimp only at hthreshold
  change F ⊆ I ∧
      (∀ c ∈ F.image (fun e => e.1 2),
        H ≤ (F.filter (fun e => e.1 2 = c)).card) ∧
      I.card ≤
        H * (I.image (fun e => e.1 2)).card +
          Nat.choose (2 * G) G *
            (F.image (fun e => e.1 2)).card at hthreshold
  rcases hthreshold with ⟨hFI, hmin, hcard⟩
  have hFE : F ⊆ E := fun _ he => hIE (hFI he)
  have hisolated' : ∀ e ∈ F, ∀ e' ∈ E,
      (e.1 0 = e'.1 0 ∨ e.1 1 = e'.1 1) → e = e' := by
    intro e he e' he' hcollision
    exact hisolated e (hFI he) e' he' hcollision
  have hclosed' : ∀ ex ∈ F, ∀ ey ∈ F, ∀ ez ∈ F,
      CWQ6CoupledCoordinatewiseSupported
          (cwQ6CoupledMixedAddress ex.1 ey.1 ez.1) →
        ∃ e' ∈ E,
          e'.1 0 = ex.1 0 ∧
          e'.1 1 = ey.1 1 ∧
          e'.1 2 = ez.1 2 := by
    intro ex hex ey hey ez hez hsupp
    exact hclosed ex (hFI hex) ey (hFI hey) ez (hFI hez) hsupp
  have hcardR : (I.card : ℝ) ≤
      (H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ) +
        (Nat.choose (2 * G) G : ℝ) *
          ((F.image (fun e => e.1 2)).card : ℝ) := by
    exact_mod_cast hcard
  have hcombined := hmass.trans hcardR
  have hmiddlePos : 0 < (Nat.choose (2 * G) G : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : G ≤ 2 * G)
  have hA :
      ((Nat.choose (2 * N) L *
          Nat.choose (2 * N - L) L : ℕ) : ℝ) *
          ((((S.card : ℝ) /
              (4 * (Nat.choose N G) ^ 2 + 1 : ℕ)) ^ d) /
            (((N + 1 : ℕ) : ℝ) ^ d)) ≤
        ((F.image (fun e => e.1 2)).card : ℝ) := by
    have hcancel :
        (Nat.choose (2 * G) G : ℝ) *
            ((Nat.choose (2 * N) L *
                Nat.choose (2 * N - L) L : ℕ) *
              ((((S.card : ℝ) /
                  (4 * (Nat.choose N G) ^ 2 + 1 : ℕ)) ^ d) /
                (((N + 1 : ℕ) : ℝ) ^ d))) ≤
          (Nat.choose (2 * G) G : ℝ) *
            ((F.image (fun e => e.1 2)).card : ℝ) := by
      exact (add_le_add_iff_left
        ((H : ℝ) * ((I.image (fun e => e.1 2)).card : ℝ))).mp hcombined
    have hscaled := (mul_le_mul_iff_of_pos_left hmiddlePos).mp hcancel
    simpa only [Nat.cast_mul] using hscaled
  exact ⟨E, F, H, hH, hFE, hisolated', hmin, hclosed',
    hHupper, hA, hmiddle⟩
