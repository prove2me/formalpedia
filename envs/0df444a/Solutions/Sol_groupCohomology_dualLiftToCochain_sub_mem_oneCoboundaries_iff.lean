-- Prove2me | solution 1 for groupCohomology.dualLiftToCochain_sub_mem_oneCoboundaries_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/64f63cfd-c4cf-51e2-87ac-5e6071334c92

import Mathlib
import Definitions.Def_GroupCohomology_TangentSpace
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_groupCohomology_dualLiftToCochain_sub_mem_oneCoboundaries_iff

universe u

open scoped DualNumber RightActions
open TrivSqZeroExt groupCohomology

theorem w2aux_conj {A G : Type u} [Ring A] [Group G] {ρ₀ : G →* Aˣ} {ρ : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ)
    (m : A) (g : G) :
    ((dualUnit (1 : Aˣ) m * ρ g * (dualUnit (1 : Aˣ) m)⁻¹ : (A[ε])ˣ) : A[ε]).snd * ↑(ρ₀ g)⁻¹
      = dualLiftToCochain ρ₀ ρ g - (↑(ρ₀ g) * m * ↑(ρ₀ g)⁻¹ - m) := by
  have hsnd : ((dualUnit (1 : Aˣ) m * ρ g * (dualUnit (1 : Aˣ) m)⁻¹ : (A[ε])ˣ) : A[ε]).snd
      = (ρ g : A[ε]).snd + m * ↑(ρ₀ g) - ↑(ρ₀ g) * m := by
    rw [Units.val_mul, Units.val_mul, snd_mul, snd_mul, fst_mul]
    simp only [dualUnit_val_fst, Units.val_one, dualUnit_val_snd, mul_one, dualUnit_inv_val_fst,
      inv_one, dualUnit_inv_val_snd, one_mul, smul_eq_mul, op_smul_eq_mul, hρ g, mul_neg]
    abel
  rw [hsnd, sub_mul, add_mul, Units.mul_inv_cancel_right]
  unfold dualLiftToCochain
  abel

theorem solution
    {k A G : Type u} [CommRing k] [Ring A] [Algebra k A] [Group G]
    {ρ₀ : G →* Aˣ} {ρ ρ' : G →* (A[ε])ˣ} (hρ : IsDualLift ρ₀ ρ) (hρ' : IsDualLift ρ₀ ρ') :
    dualLiftToCochain ρ₀ ρ - dualLiftToCochain ρ₀ ρ' ∈ coboundaries₁ (adjointRep k ρ₀)
      ↔ ∃ w : (A[ε])ˣ, (w : A[ε]).fst = 1 ∧ ∀ g, ρ' g = w * ρ g * w⁻¹ := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨dualUnit (1 : Aˣ) ((m : A)), by simp, fun g => ?_⟩

    have hmg : ↑(ρ₀ g) * (m : A) * ↑(ρ₀ g)⁻¹ - (m : A)
        = dualLiftToCochain ρ₀ ρ g - dualLiftToCochain ρ₀ ρ' g := by
      have h1 := congrFun hm g
      simp at h1
      exact h1

    have hconj : ∀ g : G, ((dualUnit (1 : Aˣ) (m : A) * ρ g
        * (dualUnit (1 : Aˣ) (m : A))⁻¹ : (A[ε])ˣ) : A[ε]).fst = ↑(ρ₀ g) := by
      intro g
      rw [Units.val_mul, Units.val_mul, fst_mul, fst_mul, dualUnit_val_fst, dualUnit_inv_val_fst,
        Units.val_one, inv_one, Units.val_one, one_mul, mul_one]
      exact hρ g

    have hcochain : (ρ' g : A[ε]).snd * ↑(ρ₀ g)⁻¹
        = ((dualUnit (1 : Aˣ) (m : A) * ρ g
            * (dualUnit (1 : Aˣ) (m : A))⁻¹ : (A[ε])ˣ) : A[ε]).snd * ↑(ρ₀ g)⁻¹ := by
      rw [w2aux_conj hρ (m : A) g, hmg]
      show dualLiftToCochain ρ₀ ρ' g = _
      abel

    apply Units.ext
    refine TrivSqZeroExt.ext ((hρ' g).trans (hconj g).symm) ?_
    have h2 := congrArg (fun x => x * (↑(ρ₀ g) : A)) hcochain
    simpa only [Units.inv_mul_cancel_right] using h2
  · rintro ⟨w, hw, hconj⟩
    refine ⟨(w : A[ε]).snd, funext fun g => ?_⟩

    have hw' : w = dualUnit (1 : Aˣ) ((w : A[ε]).snd) := by
      have h3 := eq_dualUnit_of_fst_eq (w := w) (u := 1) (by simpa using hw)
      simpa using h3
    have hkey : dualLiftToCochain ρ₀ ρ' g
        = dualLiftToCochain ρ₀ ρ g
            - (↑(ρ₀ g) * (w : A[ε]).snd * ↑(ρ₀ g)⁻¹ - (w : A[ε]).snd) := by
      have h4 : ρ' g = dualUnit (1 : Aˣ) ((w : A[ε]).snd) * ρ g
          * (dualUnit (1 : Aˣ) ((w : A[ε]).snd))⁻¹ := by
        rw [← hw']
        exact hconj g
      show (ρ' g : A[ε]).snd * ↑(ρ₀ g)⁻¹ = _
      rw [h4]
      exact w2aux_conj hρ _ g
    show ↑(ρ₀ g) * (w : A[ε]).snd * ↑(ρ₀ g)⁻¹ - (w : A[ε]).snd
        = dualLiftToCochain ρ₀ ρ g - dualLiftToCochain ρ₀ ρ' g
    rw [hkey]
    abel

end S_groupCohomology_dualLiftToCochain_sub_mem_oneCoboundaries_iff
end P2MW
export P2MW.S_groupCohomology_dualLiftToCochain_sub_mem_oneCoboundaries_iff (solution)
