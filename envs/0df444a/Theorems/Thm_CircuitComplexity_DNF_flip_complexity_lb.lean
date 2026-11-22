-- Prove2me | Theorems.Thm_CircuitComplexity_DNF_flip_complexity_lb
-- name    : CircuitComplexity.DNF.flip_complexity_lb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:10:23.946693+00:00
-- url     : https://prove2.me/theorems/a45bc297-2f2e-4e8d-9d9c-a401a190bbb8
-- title:
--   DNF: flip complexity lb
-- statement:
--   If `φ : DNF N` computes a flip-sensitive function with `N ≥ 1`,
--   then `2^{N-1} ≤ φ.complexity`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L343-L391
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Internal/NF.lean#L343-L391

module
public import Definitions.Def_LeanPool_CircuitComplexity_NF_Defs
public import Definitions.Def_LeanPool_CircuitComplexity_AON_Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_CircuitComplexity_Internal_NF
set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit true
set_option autoImplicit true
open CircuitComplexity

theorem CircuitComplexity.DNF.flip_complexity_lb (φ : DNF N) (hN : 1 ≤ N)
    (f : BitString N → Bool)
    (hcomp : ∀ x, φ.eval x = f x)
    (hflip : ∀ x (i : Fin N), f (Function.update x i (!x i)) = !f x) :
    2 ^ (N - 1) ≤ φ.complexity := by sorry
