-- Prove2me | Theorems.Thm_Falmagne_blockMarschak_necessary
-- name    : Falmagne.blockMarschak_necessary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:14:16.772428+00:00
-- url     : https://prove2.me/theorems/8df9c711-c385-4549-9fb7-cbf770329d35
-- title:
--   Falmagne: block Marschak necessary
-- statement:
--   Every random-ranking choice rule satisfies all Block–Marschak inequalities.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L62-L67
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/ChoiceMobius.lean#L62-L67

module
public import Definitions.Def_EconomicsNextProof_Representation
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_ChoiceMobius
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]
variable {l : List X} {A : Finset X} {x : X}

theorem Falmagne.blockMarschak_necessary {w : RankingLaw X} {p : Finset X → X → ℝ}
    (hw : IsRankingLaw w) (hp : Represents w p) :
    ∀ x A, x ∈ A → 0 ≤ upperMobius (fun B => p B x) A := by sorry
