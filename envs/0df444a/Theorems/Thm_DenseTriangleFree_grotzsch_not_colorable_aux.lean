-- Prove2me | Theorems.Thm_DenseTriangleFree_grotzsch_not_colorable_aux
-- name    : DenseTriangleFree.grotzsch_not_colorable_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:45:54.505573+00:00
-- url     : https://prove2.me/theorems/1ad19576-5289-41f9-b302-f24122e37d8f
-- title:
--   Dense Triangle Free: grotzsch not colorable aux
-- statement:
--   The Dense Triangle Free construction uses the grotzsch not colorable aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L60-L66
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Grotzsch.lean#L60-L66

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
set_option synthInstance.maxHeartbeats 1000000
set_option synthInstance.maxSize 100000

theorem DenseTriangleFree.grotzsch_not_colorable_aux : ∀ c0 c1 : Fin 3, c0 ≠ c1 → ∀ c2 : Fin 3, c1 ≠ c2 →
    ∀ c3 : Fin 3, c2 ≠ c3 → ∀ c4 : Fin 3, c3 ≠ c4 → c4 ≠ c0 →
    ∀ c5 : Fin 3, c5 ≠ c1 → c5 ≠ c4 → ∀ c6 : Fin 3, c6 ≠ c2 → c6 ≠ c0 →
    ∀ c7 : Fin 3, c7 ≠ c3 → c7 ≠ c1 → ∀ c8 : Fin 3, c8 ≠ c4 → c8 ≠ c2 →
    ∀ c9 : Fin 3, c9 ≠ c0 → c9 ≠ c3 →
    ∀ c10 : Fin 3, c10 ≠ c5 → c10 ≠ c6 → c10 ≠ c7 → c10 ≠ c8 → c10 ≠ c9 → False := by sorry
