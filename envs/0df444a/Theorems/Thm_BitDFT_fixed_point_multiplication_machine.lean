-- Prove2me | Theorems.Thm_BitDFT_fixed_point_multiplication_machine
-- name    : BitDFT.fixed_point_multiplication_machine
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-25T01:28:33.62074+00:00
-- url     : https://prove2.me/theorems/a60a44f0-a023-443d-9818-773d056c7956
-- title:
--   An integer multiplier implements fixed-point complex multiplication
-- statement:
--   Given any multitape machine that multiplies equal-width binary integers within a pointwise time bound $T$, there is a fixed multitape machine that multiplies two unit-disc complex fixed-point values, rounds each output coordinate toward zero, and writes the exact fixed-width result. For every precision $p\ge1$, its running time is at most $C T(p)$ for a constant $C$ independent of $p$ and the inputs. The claim isolates the machine-construction part of fixed-point multiplication; the numerical error estimate is stated separately.
-- source:
--   Machine-construction component of BitDFT.fixed_point_multiplication. It separates the exact integer arithmetic, sign handling, fixed-width serialization, and runtime composition from the numerical stability theorem BitDFT.fixed_point_product_error.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open BitDFT

theorem BitDFT.fixed_point_multiplication_machine (M : IntMul.MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), 1 ≤ p → ∀ U V : ℤ × ℤ, inDisc p U → inDisc p V →
        ∃ W : ℤ × ℤ,
          Computes A (encNat p ++ encComplex (p + 1) U ++ encComplex (p + 1) V)
            (encComplex (p + 1) W) (C * T p) ∧
          W = roundPair p (value p U * value p V) ∧ inDisc p W := by sorry
