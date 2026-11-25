-- Prove2me | Theorems.Thm_Expanders_dist_triangle_of_reachable
-- name    : Expanders.dist_triangle_of_reachable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:08:46.164461+00:00
-- url     : https://prove2.me/theorems/42137f68-8fca-4f97-a887-fd0c31eda8a6
-- title:
--   Expanders: dist triangle of reachable
-- statement:
--   The Expanders construction uses the dist triangle of reachable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L34-L39
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L34-L39

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} {G : SimpleGraph V}

theorem Expanders.dist_triangle_of_reachable {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.dist u w ≤ G.dist u v + G.dist v w := by sorry
