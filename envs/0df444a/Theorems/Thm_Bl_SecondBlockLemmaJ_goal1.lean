-- Prove2me | Theorems.Thm_Bl_SecondBlockLemmaJ_goal1
-- name    : Bl.SecondBlockLemmaJ.goal1
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T07:11:09.566205+00:00
-- url     : https://prove2.me/theorems/dbe1e580-bce8-5954-b6a4-0cb8c8174a35
-- title:
--   Second Block Lemma J: goal1
-- statement:
--   The Second Block Lemma J construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasI/Imports.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/MiscLemmasI/Imports.lean#L8-L13

import Mathlib
import Definitions.Def_Lemmata_MiscLemmasI_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Bl Bl.SecondBlockLemmaJ

theorem Bl.SecondBlockLemmaJ.goal1 {K L ι n : Type} [Field K] [Field L] [Fintype ι] [Fintype n] [DecidableEq ι]
    [DecidableEq n] (τ : K →+* L) (c : ι → n → K) (hc : LinearIndependent K c) :
    LinearIndependent L (fun a => fun i => τ (c a i)) := by sorry
