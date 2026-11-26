-- Prove2me | Theorems.Thm_DenseTriangleFree_jin_sharp
-- name    : DenseTriangleFree.jin_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:55:10.582509+00:00
-- url     : https://prove2.me/theorems/0d1e3e21-305a-50e4-b3ac-8d345d52bd06
-- title:
--   Dense Triangle Free: jin sharp
-- statement:
--   **Sharpness (Häggkvist 1982).** For every `m ≥ 1` there is a triangle-free `10m`-regular graph
--   on `29m` vertices that is not 3-colourable.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Jin.lean#L46-L49
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Jin.lean#L46-L49

module
public import Mathlib
public import Definitions.Def_JinLib_Blowup
public import Definitions.Def_JinLib_Maximal
public import Definitions.Def_JinLib_Bipartite
public import Definitions.Def_JinLib_Jin
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree

theorem DenseTriangleFree.jin_sharp (m : ℕ) (hm : 0 < m) :
    ∃ G : SimpleGraph (Fin (29 * m)), ∃ _ : DecidableRel G.Adj,
      G.CliqueFree 3 ∧ (∀ v, G.degree v = 10 * m) ∧ ¬ G.Colorable 3 := by sorry
