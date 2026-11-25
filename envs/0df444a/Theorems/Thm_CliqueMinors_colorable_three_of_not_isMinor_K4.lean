-- Prove2me | Theorems.Thm_CliqueMinors_colorable_three_of_not_isMinor_K4
-- name    : CliqueMinors.colorable_three_of_not_isMinor_K4
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:41:11.308531+00:00
-- url     : https://prove2.me/theorems/40b8b919-7b29-4629-8438-db224023ac3d
-- title:
--   Clique Minors: colorable three of not is Minor K4
-- statement:
--   **Hadwiger's conjecture for `t = 4` (Hadwiger 1943, Dirac 1952).** A finite graph without a
--   `K₄` minor is 3-colourable.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L774-L779
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L774-L779

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

theorem CliqueMinors.colorable_three_of_not_isMinor_K4 [Finite V] (G : SimpleGraph V)
    (h : ¬ IsMinor (⊤ : SimpleGraph (Fin 4)) G) : G.Colorable 3 := by sorry
