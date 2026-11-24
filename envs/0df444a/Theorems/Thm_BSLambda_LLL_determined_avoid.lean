-- Prove2me | Theorems.Thm_BSLambda_LLL_determined_avoid
-- name    : BSLambda.LLL.determined_avoid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:53:56.369813+00:00
-- url     : https://prove2.me/theorems/d64f2f90-4057-4376-abf0-651c7c7d209c
-- title:
--   LLL: determined avoid
-- statement:
--   `avoid Ev S` is determined by the union of the supports of the events indexed by `S`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L105-L110
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/LLL/Asymmetric.lean#L105-L110

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Prob
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_LLL_Asymmetric
set_option autoImplicit true
@[expose] public section
public section
open BSLambda BSLambda.LLL
variable {A : Type*} [Fintype A] [DecidableEq A]
variable {β : A → Type*} [∀ a, Fintype (β a)] [∀ a, DecidableEq (β a)] [∀ a, Nonempty (β a)]
variable {I : Type*} [Fintype I] [DecidableEq I]
omit [∀ (a : A), Nonempty (β a)]

theorem BSLambda.LLL.determined_avoid {Ev : I → Finset (Cfg β)} {supp : I → Finset A}
    (hdet : ∀ i, Determined (supp i) (Ev i)) (S : Finset I) :
    Determined (S.sup supp) (avoid Ev S) := by sorry
