-- Prove2me | solution 1 for mme_dwz_q6_112_primary_hash_family_cyclic_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T11:08:58.270891+00:00
-- url     : https://prove2.me/submissions/afd8ec34-e160-426a-b777-84b6eea8cf3c

import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_CW_q6_primary_hash_family_Ctensor_certificates
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_cyclic_value_below

open MME

universe u

/-!
The sound finite-to-asymptotic payload of DWZ Appendix A, proof of
Lemma 4.6(d), specialized to `q = 6` but uniform in the restricted split.

The premise is combinatorial only.  `CWQ6PrimaryHashFamily N L G A H`
records `A` induced shared-Z fibers of common size `H` in `2*N` coordinates,
with joint counts `L,L,G,G`.  It contains no tensor restriction and no
tau-value conclusion.  The two imported proved theorems first package those
heterogeneous fibers as genuine C-tensors of common component volume and then
perform the cyclic balanced-word extraction without choosing an invalid
common fine-coordinate trivialization.
-/
theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (N L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
        ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast
      (cyclicSymmetrization ((coupledObj K 6).kronPow (2 * N)))
      tau V := by
  obtain ⟨stars⟩ :=
    mme_CW_q6_primary_hash_family_Ctensor_certificates
      (K := K) N L G A H family
  exact mme_Ctensor_one_H_one_outer_family_cyclic_value_below
    stars tau htau V hV hVlt
