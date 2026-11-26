-- Prove2me | Theorems.Thm_Falmagne_blockMarschak_conserve
-- name    : Falmagne.blockMarschak_conserve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:24:55.332344+00:00
-- url     : https://prove2.me/theorems/3ccce5e1-ae12-536e-b387-3432cd3da03f
-- title:
--   Falmagne: block Marschak conserve
-- statement:
--   The Falmagne construction uses the block Marschak conserve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L98-L112
-- source:
--   https://github.com/Arthur742Ramos/falmagne-block-marschak-lean/blob/e6078b9b11af9010386207890fb79b792617e65e/EconomicsNextProof/Conservation.lean#L98-L112

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

theorem Falmagne.blockMarschak_conserve (p : Finset X → X → ℝ) (hp : IsChoiceRule p)
    (A : Finset X) (hA : A.Nonempty) (hproper : A ≠ univ) :
    (∑ x ∈ A, blockMarschak p x A) =
      ∑ x ∈ univ \ A, blockMarschak p x (insert x A) := by sorry
