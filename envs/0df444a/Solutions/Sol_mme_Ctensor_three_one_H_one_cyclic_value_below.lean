-- Prove2me | solution 1 for mme_Ctensor_three_one_H_one_cyclic_value_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:37:15.782408+00:00
-- url     : https://prove2.me/submissions/a1f4dc3b-8d8d-413d-ac41-636b2ab22b73

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_Ctensor_three_one_H_one_balanced_extractions_sqrt_loss
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    {X Y Z : TensorObj K 3} {H volume : ℕ}
    (certX : CTensorOneHOneCertificate X H volume)
    (certY : CTensorOneHOneCertificate Y H volume)
    (certZ : CTensorOneHOneCertificate Z H volume)
    (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < (H : ℝ) ^ 2 * (((volume ^ 3 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (threeStarCyclicProduct X Y Z) tau V := by
  let B : ℝ :=
    (H : ℝ) ^ 2 * (((volume ^ 3 : ℕ) : ℝ) ^ tau)
  have hVB : V < B := by simpa [B] using hVlt
  obtain ⟨C, hC, hfinite⟩ :=
    mme_Ctensor_three_one_H_one_balanced_extractions_sqrt_loss
      certX certY certZ hH hvolume tau htau
  let s : ℕ → ℕ := fun m => H * m
  have hs : Tendsto s atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with m hm
    dsimp [s]
    exact hm.trans (by
      simpa [mul_comm] using Nat.le_mul_of_pos_right m hH)
  have hgap0 :=
    mme_strict_pow_absorbs_sqrt_exp_loss V B C hV hVB hC
  have hgap :
      ∀ᶠ m : ℕ in atTop,
        V ^ (s m) ≤ B ^ (s m) *
          Real.exp
            (-C * Real.sqrt ((((s m) + 1 : ℕ) : ℝ))) :=
    hs.eventually hgap0
  apply mme_HasTauValueAtLeast_of_cofinal_finite_extractions
    (T := threeStarCyclicProduct X Y Z) tau V hV s hs
    (fun _ => (0 : ℝ)) tendsto_const_nhds
  filter_upwards [hfinite, hgap] with m hm hmgap
  dsimp only at hm
  obtain ⟨k, a, b, c, hrestrict, hcount⟩ := hm
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  simp only [sub_zero, mul_one]
  exact hmgap.trans (by
    change B ^ (s m) *
        Real.exp
          (-C * Real.sqrt ((((s m) + 1 : ℕ) : ℝ))) ≤
      ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)
    simpa [B, s] using hcount)
