-- Prove2me | Theorems.Thm_DenseTriangleFree_grotzsch_indep_weight
-- name    : DenseTriangleFree.grotzsch_indep_weight
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:57.516325+00:00
-- url     : https://prove2.me/theorems/8ee9ebb9-267a-4c88-b1e8-7cdaecd4af1c
-- title:
--   Dense Triangle Free: grotzsch indep weight
-- statement:
--   Every independent set of the Grötzsch graph has weight at most `10`.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L93-L116
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L93-L116

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree

theorem DenseTriangleFree.grotzsch_indep_weight (s : Fin 11 → Prop) [DecidablePred s]
    (hs : ∀ i j, grotzsch.Adj i j → s i → s j → False) :
    ∑ i, (if s i then grotzschWt i else 0) ≤ 10 := by sorry
