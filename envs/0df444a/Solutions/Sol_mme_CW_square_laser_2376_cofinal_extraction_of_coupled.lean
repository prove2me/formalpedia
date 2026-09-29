-- Prove2me | solution 1 for mme_CW_square_laser_2376_cofinal_extraction_of_coupled
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:06:12.957206+00:00
-- url     : https://prove2.me/submissions/b5209056-b9f8-4c6c-b7a1-a7af128fafd8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecificLimits.Basic
import Theorems.Thm_mme_CW_2376_integer_profile
import Theorems.Thm_mme_CW_square_laser_2376_profile_pruning
import Theorems.Thm_mme_HasTauValueAtLeast_to_cofinal_finite_extractions

open MME BigOperators Filter

universe u

/-!
Reduction of the exact-profile cofinal extraction to:

* the generic sequential selector for a tau-value witness;
* the exact integer profile; and
* the finite five-grade laser/pruning construction.

The total relative error is the sum of the vanishing laser loss and the exact
error incurred by Kronecker-powering the coupled witness `616627` times.
-/

theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (hcoupled :
      HasSymmetricTauValueAtLeast (coupledObj K 6) tau
        ((2 : ℝ) ^ ((2 : ℝ) / 3) *
         (6 : ℝ) ^ tau *
         (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3)))) :
    ∃ (m : ℕ → ℕ) (error : ℕ → ℝ),
      Tendsto m atTop atTop ∧
      Tendsto error atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (x y z : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
            ((CWObj K 6).kronPow (6000000 * m n)) ∧
          (auxiliaryRHS 6 tau
              cw2376_a cw2376_b cw2376_c cw2376_d) ^ (3000000 * m n) *
              (1 - error n) ≤
            ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  change HasTauValueAtLeast
      (cyclicSymmetrization (coupledObj K 6)) tau
      (((2 : ℝ) ^ ((2 : ℝ) / 3) *
        (6 : ℝ) ^ tau *
        (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) ^ (3 : ℕ)) at hcoupled
  obtain ⟨m, delta, hm, hdelta, hdelta_pos, hwitness⟩ :=
    mme_HasTauValueAtLeast_to_cofinal_finite_extractions
      (cyclicSymmetrization (coupledObj K 6)) tau
      (((2 : ℝ) ^ ((2 : ℝ) / 3) *
        (6 : ℝ) ^ tau *
        (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) ^ (3 : ℕ))
      hcoupled
  obtain ⟨laserError, hlaser, _hlaser_bounds, hprofile⟩ :=
    mme_CW_square_laser_2376_profile_pruning (K := K) tau htau
  let error : ℕ → ℝ := fun n =>
    laserError (m n) +
      (1 - (1 - delta n) ^ (616627 : ℕ))
  have hamplified_error :
      Tendsto (fun n : ℕ => 1 - (1 - delta n) ^ (616627 : ℕ))
        atTop (nhds 0) := by
    have hbase :
        Tendsto (fun n : ℕ => 1 - delta n) atTop (nhds (1 - 0)) :=
      tendsto_const_nhds.sub hdelta
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using hone.sub (hbase.pow (616627 : ℕ))
  have herror : Tendsto error atTop (nhds 0) := by
    simpa [error] using (hlaser.comp hm).add hamplified_error
  have hdelta_le_one : ∀ᶠ n : ℕ in atTop, delta n ≤ 1 := by
    exact (((tendsto_order.1 hdelta).2 (1 : ℝ) one_pos).mono fun _ h => h.le)
  refine ⟨m, error, hm, herror, ?_⟩
  filter_upwards [hm.eventually hprofile, hdelta_le_one] with n hn hdelta_one
  obtain ⟨kc, xc, yc, zc, hrestrict, hweight⟩ := hwitness n
  have _hprofile_exact := mme_CW_2376_integer_profile (m n)
  simpa [error] using
    (hn (delta n) (hdelta_pos n) hdelta_one
      kc xc yc zc hrestrict hweight)
