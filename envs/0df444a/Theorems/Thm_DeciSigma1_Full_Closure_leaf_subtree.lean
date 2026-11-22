-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_leaf_subtree
-- name    : DeciSigma1.Full.Closure.leaf_subtree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:41:22.598572+00:00
-- url     : https://prove2.me/theorems/4e5320bb-7513-4305-8f4e-799a52ceb71a
-- title:
--   Closure: leaf subtree
-- statement:
--   Subtree cones are residuals with signs shifted by the path polarity.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/RegularCones.lean#L46-L63
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/RegularCones.lean#L46-L63

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Classes
public import Mathlib.Data.Finite.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_RegularCones
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Semantics DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Full.Closure.leaf_subtree (c : Fin n → Bool) {t u : Tree n} {w : List (Fin n)}
    (h : t.subtree w = some u) (s : Bool) :
    residual (leaf c t s) w = leaf c u (Bool.xor s (polarity c w)) := by sorry
