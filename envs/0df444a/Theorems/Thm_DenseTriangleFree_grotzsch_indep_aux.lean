-- Prove2me | Theorems.Thm_DenseTriangleFree_grotzsch_indep_aux
-- name    : DenseTriangleFree.grotzsch_indep_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:50.673489+00:00
-- url     : https://prove2.me/theorems/25ae63b4-e68a-450b-9930-d10047558c59
-- title:
--   Dense Triangle Free: grotzsch indep aux
-- statement:
--   The Dense Triangle Free construction uses the grotzsch indep aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L87-L90
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L87-L90

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
set_option maxRecDepth 100000

theorem DenseTriangleFree.grotzsch_indep_aux : ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool,
    grotzschIndepB ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] = true →
      grotzschWtB ![b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] ≤ 10 := by sorry
