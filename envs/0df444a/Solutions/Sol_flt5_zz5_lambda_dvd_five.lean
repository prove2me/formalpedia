-- Prove2me | solution 1 for flt5_zz5_lambda_dvd_five
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-13T10:17:11.100961+00:00
-- url     : https://prove2.me/submissions/ee26435a-f744-458c-9ff6-cd40af4c8c31

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Data.Int.Basic

-- Proof: (1-ζ) | 5 in ZZ5
-- Witness: (1-ζ)*((1-ζ^2)*((1-ζ^3)*(1-ζ^4))) = 5
-- From ζ^5=1 and (ζ-1)*(ζ^4+ζ^3+ζ^2+ζ+1)=0, ζ≠1 (primitive), so Φ₅(ζ)=0.
-- Goal (after refine): 5 = (1-ζ)*((1-ζ²)*((1-ζ³)*(1-ζ⁴)))
-- linear_combination: 5 - (1-ζ)*... = -(ζ^5-ζ^4-ζ^3+3)*(ζ^5-1) + (ζ^4+ζ^3+ζ^2+ζ+1)
--   so: linear_combination -(ζ^5-ζ^4-ζ^3+3)*hζ5 + hphi

noncomputable section

abbrev ZZ5lam3 := NumberField.RingOfIntegers (CyclotomicField 5 ℚ)

instance : IsCyclotomicExtension {5} ℚ (CyclotomicField 5 ℚ) :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField (CyclotomicField 5 ℚ) :=
  IsCyclotomicExtension.numberField {5} ℚ (CyclotomicField 5 ℚ)

theorem solution (ζ : ZZ5lam3)
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField 5 ℚ) 5) :
    (1 - ζ) ∣ (5 : ZZ5lam3) := by
  refine ⟨(1 - ζ ^ 2) * ((1 - ζ ^ 3) * (1 - ζ ^ 4)), ?_⟩
  -- Goal: 5 = (1 - ζ) * ((1 - ζ^2) * ((1 - ζ^3) * (1 - ζ^4)))
  have hζ5 : ζ ^ 5 = 1 := by
    apply_fun (↑· : ZZ5lam3 → CyclotomicField 5 ℚ) using Subtype.val_injective
    push_cast
    exact hζ.pow_eq_one
  have hphi : ζ ^ 4 + ζ ^ 3 + ζ ^ 2 + ζ + 1 = 0 := by
    apply_fun (↑· : ZZ5lam3 → CyclotomicField 5 ℚ) using Subtype.val_injective
    push_cast
    set z := (ζ : CyclotomicField 5 ℚ)
    have hz5 : z ^ 5 = 1 := hζ.pow_eq_one
    have hfactor : (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = 0 := by
      have : (z - 1) * (z ^ 4 + z ^ 3 + z ^ 2 + z + 1) = z ^ 5 - 1 := by ring
      rw [this, hz5, sub_self]
    rcases mul_eq_zero.mp hfactor with h1 | h2
    · exfalso
      have hne : z ≠ 1 := by
        intro heq
        -- orderOf z = 5 (from IsPrimitiveRoot), but orderOf 1 = 1
        have hord := hζ.eq_orderOf
        rw [heq, orderOf_one] at hord
        norm_num at hord
      exact hne (sub_eq_zero.mp h1)
    · exact h2
  -- linear_combination proof:
  -- 5 - (1-ζ)*((1-ζ²)*((1-ζ³)*(1-ζ⁴))) = -(ζ^5-ζ^4-ζ^3+3)*(ζ^5-1) + (ζ^4+ζ^3+ζ^2+ζ+1)
  linear_combination -(ζ ^ 5 - ζ ^ 4 - ζ ^ 3 + 3) * hζ5 + hphi

end
