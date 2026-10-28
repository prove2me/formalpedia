-- Prove2me | Theorems.Thm_BitDFT_fixed_point_multiplication_machine_core
-- name    : BitDFT.fixed_point_multiplication_machine_core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-25T01:37:17.355726+00:00
-- url     : https://prove2.me/theorems/14a0032b-8ebb-4e97-b4bc-f987d1f04e83
-- title:
--   An integer multiplier computes the exact rounded complex product
-- statement:
--   Given a multitape integer multiplier with pointwise time bound $T$, there is a fixed multitape machine that computes the exact coordinatewise rounded product of two complex fixed-point inputs. For every precision $p\ge1$ and inputs in the unit disc, it runs within $C T(p)$ transitions for one constant $C$. This is the algorithmic core; the range-preservation property is handled separately.
-- source:
--   Core machine-construction obligation for BitDFT.fixed_point_multiplication_machine, separated from the proved unit-disc range lemma BitDFT.roundPair_product_disc.

import Definitions.Def_BitDFT_Numerics
import Definitions.Def_IntMul_HvdH_KronMul
set_option autoImplicit false
noncomputable section
open BitDFT

theorem BitDFT.fixed_point_multiplication_machine_core (M : IntMul.MultitapeTM) (T : ℕ → ℝ)
    (hM : Multiplier M T) :
    ∃ A : IntMul.MultitapeTM, ∃ C : ℝ, 0 < C ∧
      ∀ (p : ℕ), 1 ≤ p → ∀ U V : ℤ × ℤ, inDisc p U → inDisc p V →
        ∃ W : ℤ × ℤ,
          Computes A (encNat p ++ encComplex (p + 1) U ++ encComplex (p + 1) V)
            (encComplex (p + 1) W) (C * T p) ∧
          W = roundPair p (value p U * value p V) := by sorry
