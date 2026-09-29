-- Prove2me | solution 1 for mme_Ctensor_one_H_one_balanced_extractions_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:23:45.147641+00:00
-- url     : https://prove2.me/submissions/02b02d05-a2fb-49bb-9b91-15614b0df7e1

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_tau_value
import Definitions.Def_mme_CW_coupled_value
import Theorems.Thm_mme_Ctensor_balanced_cyclic_induced_matching_extraction
import Theorems.Thm_mme_Ctensor_balanced_weight_sqrt_loss

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := H * m
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization T).kronPow R) ∧
          (((H : ℝ) ^ 2 *
                (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
              Real.exp
                (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  obtain ⟨C, hC, hweight⟩ :=
    mme_Ctensor_balanced_weight_sqrt_loss
      H volume hH hvolume tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hweight] with m hm
  dsimp only at hm ⊢
  obtain ⟨k, a, b, c, hrestrict, hk, hvol⟩ :=
    mme_Ctensor_balanced_cyclic_induced_matching_extraction
      cert hH m
  refine ⟨k, a, b, c, hrestrict, ?_⟩
  let R : ℕ := H * m
  let W : ℕ :=
    Nat.card
      {w : Fin R → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}
  let q : ℝ := (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau)
  have hq : 0 ≤ q := by
    dsimp [q]
    positivity
  have hsum :
      (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) =
        (k : ℝ) * q := by
    dsimp [q, R]
    simp_rw [hvol]
    simp
  rw [hsum]
  refine hm.trans ?_
  apply mul_le_mul_of_nonneg_right
  · simpa [W, R] using hk
  · exact hq
