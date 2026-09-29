-- Prove2me | solution 1 for exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:14.293936+00:00
-- url     : https://prove2.me/submissions/bd0f267d-3d99-5fff-8681-06c434cf4a54

import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one

set_option autoImplicit false

local notation "Qbar" => AlgebraicClosure ℚ

theorem solution (ℓ : ℕ) (hℓ : ℓ.Prime)
    (A : ValuationSubring Qbar) (hA : A.LiesOverPrime ℓ) :
    ∃ σ ∈ A.inertiaSubgroupIn ℚ, ∃ n a : ℕ,
      (∀ μ : Qbar, μ ^ ℓ ^ n = 1 → σ μ = μ ^ a) ∧ ¬ a ≡ 1 [MOD ℓ ^ n] := by
  rcases eq_or_ne ℓ 2 with h2 | h2
  · subst h2
    obtain ⟨σ, hσI, hσ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow_three_of_pow_four_eq_one A hA
    refine ⟨σ, hσI, 2, 3, ?_, ?_⟩
    · intro μ hμ
      norm_num at hμ
      exact hσ μ hμ
    · decide
  · haveI : Fact ℓ.Prime := ⟨hℓ⟩
    have hℓ3 : 3 ≤ ℓ := by
      have := hℓ.two_le
      omega
    obtain ⟨σ, hσI, hσ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow A hℓ hA (-1)
    refine ⟨σ, hσI, 1, ((-1 : (ZMod ℓ)ˣ) : ZMod ℓ).val, ?_, ?_⟩
    · intro μ hμ
      rw [pow_one] at hμ
      exact hσ μ hμ
    · intro hcong
      have hval : ((-1 : (ZMod ℓ)ˣ) : ZMod ℓ).val = ℓ - 1 := by
        have hcoe : ((-1 : (ZMod ℓ)ˣ) : ZMod ℓ) = -1 := by simp
        rw [hcoe]
        obtain ⟨m, rfl⟩ : ∃ m, ℓ = m + 1 := ⟨ℓ - 1, by omega⟩
        simp [ZMod.val_neg_one]
      rw [hval, pow_one] at hcong
      have hmod : (ℓ - 1) % ℓ = 1 % ℓ := hcong
      have ha : (ℓ - 1) % ℓ = ℓ - 1 := Nat.mod_eq_of_lt (by omega)
      have hb : 1 % ℓ = 1 := Nat.mod_eq_of_lt (by omega)
      omega

end S_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one
end P2MW
export P2MW.S_exists_inertiaSubgroupIn_rootOfUnity_pow_ne_one (solution)
