-- Prove2me | Theorems.Thm_CliqueMinors_colorable_two_of_not_isMinor_K3
-- name    : CliqueMinors.colorable_two_of_not_isMinor_K3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:06.08845+00:00
-- url     : https://prove2.me/theorems/99df4793-e384-492f-933b-814465b74abe
-- title:
--   Clique Minors: colorable two of not is Minor K3
-- statement:
--   **Hadwiger's conjecture for `t = 3`.** A finite graph without a `K₃` minor (a forest) is
--   2-colourable.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L765-L770
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L765-L770

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}

theorem CliqueMinors.colorable_two_of_not_isMinor_K3 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 3)) G) : G.Colorable 2 := by sorry
