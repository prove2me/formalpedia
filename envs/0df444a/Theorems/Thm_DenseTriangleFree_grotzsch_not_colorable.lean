-- Prove2me | Theorems.Thm_DenseTriangleFree_grotzsch_not_colorable
-- name    : DenseTriangleFree.grotzsch_not_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:05.127915+00:00
-- url     : https://prove2.me/theorems/8d90574f-c411-497d-926c-f24448f03a3b
-- title:
--   Dense Triangle Free: grotzsch not colorable
-- statement:
--   The Grötzsch graph is not 3-colourable.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L69-L75
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L69-L75

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree

theorem DenseTriangleFree.grotzsch_not_colorable : ¬ grotzsch.Colorable 3 := by sorry
