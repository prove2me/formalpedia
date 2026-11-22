-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_toCSDOf_good
-- name    : Formalism.L2.Col.GSD.toCSDOf_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:02:46.468036+00:00
-- url     : https://prove2.me/theorems/d8a7e0b2-31b7-487f-a73f-851a8e68790a
-- title:
--   GSD: to CSDOf good
-- statement:
--   The GSD construction uses the to CSDOf good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L223-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L223-L240

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumBridge
import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
attribute [instance] GSD.grpG GSD.actD GSD.addV GSD.modV GSD.modOV GSD.towV GSD.finιV GSD.decιV
open Formalism.L2.Col.GSD
variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K)

theorem Formalism.L2.Col.GSD.toCSDOf_good {n : ℕ} (G : S.Good n) (s : S.Sec) : (S.toCSDOf G.ok s).Good n := by sorry
