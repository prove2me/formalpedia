-- Prove2me | Theorems.Thm_BandParity_sum_Ioc_alt
-- name    : BandParity.sum_Ioc_alt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:01:25.742791+00:00
-- url     : https://prove2.me/theorems/a881b702-9b5c-5fcb-a4f2-88c81d03c4d7
-- title:
--   Band Parity: sum Ioc alt
-- statement:
--   The Band Parity construction uses the sum Ioc alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L137-L144
-- source:
--   https://github.com/jkfarland-bot/Bandparity/blob/890a306dcb94aaf290ca390e553f9c2ba39de246/BandParity/Laws.lean#L137-L144

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
omit hp

theorem BandParity.sum_Ioc_alt (m : ℕ) : ∑ v ∈ Ioc 0 (2 * m), (-1 : ℤ) ^ v = 0 := by sorry
