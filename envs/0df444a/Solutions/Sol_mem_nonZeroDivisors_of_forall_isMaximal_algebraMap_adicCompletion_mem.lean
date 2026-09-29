-- Prove2me | solution 1 for mem_nonZeroDivisors_of_forall_isMaximal_algebraMap_adicCompletion_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/a0ada35f-c905-5dea-9452-1d7edeace901

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_mem_nonZeroDivisors_of_forall_isMaximal_algebraMap_adicCompletion_mem

set_option autoImplicit false

theorem solution
    (B : Type) [CommRing B] [IsNoetherianRing B] (b : B)
    (h : ∀ (𝔪 : Ideal B), 𝔪.IsMaximal →
      algebraMap B (AdicCompletion 𝔪 B) b ∈ nonZeroDivisors (AdicCompletion 𝔪 B)) :
    b ∈ nonZeroDivisors B := by
  classical
  rw [mem_nonZeroDivisors_iff_right]
  intro c hcb
  apply eq_zero_of_localization c
  intro J hJ

  have hc0 : algebraMap B (AdicCompletion J B) c = 0 := by
    have h1 : algebraMap B (AdicCompletion J B) c * algebraMap B (AdicCompletion J B) b = 0 := by
      rw [← map_mul, hcb, map_zero]
    exact (mem_nonZeroDivisors_iff_right.mp (h J hJ)) _ h1
  have hof : AdicCompletion.of J B c = 0 := by
    rwa [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self_apply] at hc0

  have hcn : ∀ n : ℕ, c ∈ J ^ n := by
    intro n
    have h2 : (AdicCompletion.of J B c).1 n = 0 := by rw [hof]; rfl
    rw [AdicCompletion.of_apply] at h2
    have h3 : c ∈ (J ^ n • ⊤ : Submodule B B) := (Submodule.Quotient.mk_eq_zero _).mp h2
    rwa [Ideal.smul_eq_mul, Ideal.mul_top] at h3

  have hmem : algebraMap B (Localization.AtPrime J) c ∈
      ⨅ n : ℕ, IsLocalRing.maximalIdeal (Localization.AtPrime J) ^ n := by
    rw [Ideal.mem_iInf]
    intro n
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (hcn n)
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top] at hmem
  exact (Submodule.mem_bot _).mp hmem

end S_mem_nonZeroDivisors_of_forall_isMaximal_algebraMap_adicCompletion_mem
end P2MW
export P2MW.S_mem_nonZeroDivisors_of_forall_isMaximal_algebraMap_adicCompletion_mem (solution)
