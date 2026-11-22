-- Prove2me | Theorems.Thm_Bl_SecondBlockLemmaA_goal1
-- name    : Bl.SecondBlockLemmaA.goal1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:46.97009+00:00
-- url     : https://prove2.me/theorems/005efaad-0ffb-4e5d-b60b-31284bec25aa
-- title:
--   Second Block Lemma A: goal1
-- statement:
--   The Second Block Lemma A construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/SecondBlockLemmaA/Imports.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/SecondBlockLemmaA/Imports.lean#L7-L20

import Mathlib
import Definitions.Def_Lemmata_SecondBlockLemmaA_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2
open Bl Bl.SecondBlockLemmaA

theorem Bl.SecondBlockLemmaA.goal1 :
  ∀ {O : Type u_1} [inst : CommRing.{u_1} O] [inst_1 : IsDomain.{u_1} O] [inst_2 : IsDiscreteValuationRing.{u_1} O]
  {ι : Type u_2} (s : Finset.{u_2} ι) (a : ι → O),
  Eq.{1}
    (DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O)
      (Finset.prod.{u_2, u_1} s fun (i : ι) ↦ a i))
    (Finset.sum.{u_2, 0} s fun (i : ι) ↦
      DFunLike.coe.{u_1 + 1, u_1 + 1, 1} (IsDiscreteValuationRing.addVal.{u_1} O) (a i)) := by sorry
