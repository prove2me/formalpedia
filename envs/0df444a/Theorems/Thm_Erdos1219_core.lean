-- Prove2me | Theorems.Thm_Erdos1219_core
-- name    : Erdos1219.core
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T05:49:16.491796+00:00
-- url     : https://prove2.me/theorems/312055d5-5776-4119-9024-51c67cd48f93
-- title:
--   Erdos1219: core
-- statement:
--   The core theorem: for a symmetric pair colouring of a set of size `Σ_k 2^{ℵ_{n_k}}`, there
--   is a homogeneous set of size `ℵ_ω`.
--
--   Source: https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L430-L458
-- source:
--   https://github.com/jbaelaw/erdos1219-lean/blob/00e696a9cd2bbd8cad33d2cdc90ad385058c1466/Erdos1219/Canonization.lean#L430-L458

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u

theorem Erdos1219.core {V : Type u} (f : V → V → Bool) (hf : ∀ x y, f x y = f y x)
    (n : ℕ → ℕ) (hn : StrictMono n)
    (hpow : StrictMono fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k))
    (h0 : ℵ_ ω < (2 : Cardinal.{u}) ^ ℵ_ (n 0))
    (hV : #V = Cardinal.sum fun k => (2 : Cardinal.{u}) ^ ℵ_ (n k)) :
    ∃ (c : Bool) (H : Set V), #H = ℵ_ ω ∧ Homog f c H := by sorry
