-- Prove2me | Theorems.Thm_BandParity_zero_ne_neg_gi
-- name    : BandParity.zero_ne_neg_gi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:03:41.016621+00:00
-- url     : https://prove2.me/theorems/9e32b315-2fc7-4c33-a216-9e8221842735
-- title:
--   Band Parity: zero ne neg gi
-- statement:
--   The Band Parity construction uses the zero ne neg gi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L167-L167
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L167-L167

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

theorem BandParity.zero_ne_neg_gi : (0 : GaussianInt) ≠ -gi := by sorry
