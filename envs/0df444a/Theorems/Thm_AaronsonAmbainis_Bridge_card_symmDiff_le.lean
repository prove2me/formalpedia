-- Prove2me | Theorems.Thm_AaronsonAmbainis_Bridge_card_symmDiff_le
-- name    : AaronsonAmbainis.Bridge.card_symmDiff_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T23:03:05.638568+00:00
-- url     : https://prove2.me/theorems/41c70dbf-ae30-4695-be1b-f2b1e239d2c6
-- title:
--   Bridge: card symm Diff le
-- statement:
--   The Bridge construction uses the card symm Diff le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L59-L66
-- source:
--   https://github.com/physical-superintelligence/aaronson-ambainis/blob/2a6ceaef872ae993708950f951989134084b851a/AaronsonAmbainis/Bridge/Algebra.lean#L59-L66

import Definitions.Def_AaronsonAmbainis_Bridge_Fourier
import Definitions.Def_AaronsonAmbainis_Bridge_Algebra
set_option autoImplicit true
open AaronsonAmbainis AaronsonAmbainis.Bridge
open Finset
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [Fintype ι]

theorem AaronsonAmbainis.Bridge.card_symmDiff_le (S T : Finset ι) : (symmDiff S T).card ≤ S.card + T.card := by sorry
