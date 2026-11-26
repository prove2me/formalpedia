-- Prove2me | Theorems.Thm_Falmagne_represented_isChoiceRule
-- name    : Falmagne.represented_isChoiceRule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:03.552108+00:00
-- url     : https://prove2.me/theorems/77cf992b-3a61-467c-955e-b7ff0542c0ff
-- title:
--   Falmagne: represented is Choice Rule
-- statement:
--   A ranking law always generates a normalized stochastic choice rule.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Representation.lean#L38-L61
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Representation.lean#L38-L61

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Representation
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}

theorem Falmagne.represented_isChoiceRule {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : IsRankingLaw w) (hp : Represents w p) : IsChoiceRule p := by sorry
