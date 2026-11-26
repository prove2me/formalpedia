-- Prove2me | Theorems.Thm_BrooksTheorem_colorable_of_cliqueFree
-- name    : BrooksTheorem.colorable_of_cliqueFree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:14.86054+00:00
-- url     : https://prove2.me/theorems/6c1813ca-f863-4c9c-8a9a-50e0f21ad462
-- title:
--   Brooks Theorem: colorable of clique Free
-- statement:
--   **Brooks' theorem, clique form.** For `k ≥ 3`, a finite graph of maximum degree at most `k`
--   without a `(k + 1)`-clique is `k`-colourable.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Brooks.lean#L34-L41
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Brooks.lean#L34-L41

module
public import Mathlib
public import Definitions.Def_BrooksLib_BrooksLow
public import Definitions.Def_BrooksLib_Brooks
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BrooksTheorem
variable {V : Type*}

theorem BrooksTheorem.colorable_of_cliqueFree [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hk : 3 ≤ k) (hΔ : G.maxDegree ≤ k) (hK : G.CliqueFree (k + 1)) : G.Colorable k := by sorry
