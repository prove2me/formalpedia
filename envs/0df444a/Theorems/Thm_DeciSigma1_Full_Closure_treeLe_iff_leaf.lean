-- Prove2me | Theorems.Thm_DeciSigma1_Full_Closure_treeLe_iff_leaf
-- name    : DeciSigma1.Full.Closure.treeLe_iff_leaf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:38:35.689843+00:00
-- url     : https://prove2.me/theorems/2194ac59-99fd-49c3-9671-dc29263f1cf8
-- title:
--   Closure: tree Le iff leaf
-- statement:
--   `t ≤ u` with variance `c` exactly when the `⊤`-cone of `t` is contained in that of `u` and the
--   `⊥`-cone of `u` in that of `t`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L113-L132
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Closure/Basic.lean#L113-L132

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Definitions.Def_LeanPool_DeciSigma1_Full_Closure_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Full DeciSigma1.Full.Closure
open DeciSigma1.Full.Models DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Full.Closure.treeLe_iff_leaf (c : Fin n → Bool) (t u : Semantics.Tree n) :
    Tree.Le c t u ↔ leaf c t false ⊆ leaf c u false ∧
      leaf c u true ⊆ leaf c t true := by sorry
