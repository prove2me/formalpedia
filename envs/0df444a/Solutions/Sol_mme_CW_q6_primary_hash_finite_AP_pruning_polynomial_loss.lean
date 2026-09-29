-- Prove2me | solution 1 for mme_CW_q6_primary_hash_finite_AP_pruning_polynomial_loss
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T20:21:02.738189+00:00
-- url     : https://prove2.me/submissions/d326d61b-6c58-488e-a23c-58ae133b7dc4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_mme_CW_q6_finite_hash_isolated_lower_bounded_fibers
import Theorems.Thm_mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family

open MME

/-- The target follows exactly from the quantitative finite hash witness and
the proved deterministic common-H extraction/enumeration theorem. -/
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
          ∃ A H : ℕ,
            ∃ family : CWQ6PrimaryHashFamily N L G A H,
              H ≤ 4 ^ N ∧
              (Zcount : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                (A : ℝ) ∧
              (middle : ℝ) *
                  ((((S.card : ℝ) / (Mmod : ℝ)) ^ d) /
                    (((N + 1 : ℕ) : ℝ) ^ d)) ≤
                4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  obtain ⟨d, hd, hhash⟩ :=
    mme_CW_q6_finite_hash_isolated_lower_bounded_fibers
  refine ⟨d, hd, ?_⟩
  intro N L G hregular hprofile
  dsimp only
  intro S hSrange hSfree hSpos
  obtain ⟨E, F, H, hH, hFE, hisolated, hmin, hclosed,
      hHupper, hA, hmiddle⟩ :=
    hhash N L G hregular hprofile S hSrange hSfree hSpos
  let A : ℕ := (F.image (fun e => e.1 2)).card
  have hfamily : Nonempty (CWQ6PrimaryHashFamily N L G A H) := by
    dsimp [A]
    exact mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
      N L G H E F hH hFE hisolated hmin hclosed
  exact ⟨A, H, Classical.choice hfamily, hHupper, hA, hmiddle⟩
