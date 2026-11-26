-- Prove2me | Theorems.Thm_BandParity_sum_filter_val
-- name    : BandParity.sum_filter_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:11.21313+00:00
-- url     : https://prove2.me/theorems/2f2fd6e0-c584-4781-9f8b-2089e8694b8d
-- title:
--   Band Parity: sum filter val
-- statement:
--   Sums over residues with a condition on the least residue are sums over `ℕ`.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L121-L134
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L121-L134

module
public import Definitions.Def_BandParity_Defs
public import Definitions.Def_BandParity_Matching
public import Definitions.Def_BandParity_Laws
set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]

theorem BandParity.sum_filter_val {R : Type*} [AddCommMonoid R] (P : ℕ → Prop) [DecidablePred P]
    (g : ℕ → R) :
    ∑ x ∈ univ.filter (fun x : ZMod p => P x.val), g x.val =
      ∑ v ∈ (range p).filter P, g v := by sorry
