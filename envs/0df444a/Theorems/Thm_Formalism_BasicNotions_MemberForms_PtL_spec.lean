-- Prove2me | Theorems.Thm_Formalism_BasicNotions_MemberForms_PtL_spec
-- name    : Formalism.BasicNotions.MemberForms.PtL_spec
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:32:45.483019+00:00
-- url     : https://prove2.me/theorems/6a137890-d040-45e2-b5f9-060c9f7b4b6a
-- title:
--   Member Forms: Pt L spec
-- statement:
--   The Member Forms construction uses the Pt L spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataForms.lean#L269-L271
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataForms.lean#L269-L271

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
import Definitions.Def_Formalism_LocalRingCardinality_DataArith
import Definitions.Def_Formalism_LocalRingCardinality_DataKernels
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_LocalRingCardinality_DataForms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions
open NumberField
open Formalism.BasicNotions.MemberForms
attribute [instance] MemberForms.lvAcg MemberForms.lvMod MemberForms.lkAcg MemberForms.lkMod
  MemberForms.clsPFin MemberForms.stabPGrp MemberForms.stabPFin
variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

theorem Formalism.BasicNotions.MemberForms.PtL_spec (h : M.PRat) (x : (M.lat R.m).V) :
    M.ptEmb (M.PtL h x) = P.lowerMap (P.evz (M.emb R.m x)) := by sorry
