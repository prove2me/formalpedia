-- Prove2me | Theorems.Thm_Falmagne_blockMarschak_total
-- name    : Falmagne.blockMarschak_total
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:52.33433+00:00
-- url     : https://prove2.me/theorems/7be089c2-3486-5157-b19a-31824b1c52d1
-- title:
--   Falmagne: block Marschak total
-- statement:
--   Normalization turns the total Möbius mass into a full-set point mass.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L77-L96
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L77-L96

module
public import Definitions.Def_EconomicsNextProof_Basic
public import Definitions.Def_EconomicsNextProof_Mobius
public import Definitions.Def_EconomicsNextProof_Path
public import Definitions.Def_EconomicsNextProof_Conservation
set_option autoImplicit true
@[expose] public section
public section
open Falmagne
open Finset
open EconomicsNextProof
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem Falmagne.blockMarschak_total (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (hA : A.Nonempty) :
    ∑ x : X, blockMarschak p x A = if A = univ then 1 else 0 := by sorry
