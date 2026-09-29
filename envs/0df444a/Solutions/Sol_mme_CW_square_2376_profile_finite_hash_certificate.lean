-- Prove2me | solution 1 for mme_CW_square_2376_profile_finite_hash_certificate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T15:58:24.913275+00:00
-- url     : https://prove2.me/submissions/dadb324c-07bb-46d3-8aa0-5ff1d1d6372a

import Theorems.Thm_mme_CW_square_q6_five_grade_orbit_certificate
import Theorems.Thm_mme_CW_square_2376_profile_finite_hash_of_orbit_certificate

open MME Filter

universe u

theorem solution
    {K : Type u} [Field K] :
    ∀ᶠ m : ℕ in atTop,
      ∃ s : ℕ,
        TensorObj.Restrict
          (TensorObj.bigAdd
            (fun _ : Fin s => cw2376ProfileCore K m))
          ((CWObj K 6).kronPow (6000000 * m)) ∧
        (cw2376ProfileCountBase *
            Real.exp (-(cw2376ProfileRate m))) ^
            (3000000 * m) ≤ (s : ℝ) := by
  obtain ⟨cert⟩ :=
    mme_CW_square_q6_five_grade_orbit_certificate (K := K)
  exact
    mme_CW_square_2376_profile_finite_hash_of_orbit_certificate cert
