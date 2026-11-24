-- Prove2me | Theorems.Thm_Formalism_L2_Col_GSD_mem_intOf
-- name    : Formalism.L2.Col.GSD.mem_intOf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:46.82575+00:00
-- url     : https://prove2.me/theorems/36443681-b1a9-416f-80f5-052fd8329c96
-- title:
--   GSD: mem int Of
-- statement:
--   The GSD construction uses the mem int Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/RhoEqOfSmulEq.lean#L124-L126

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

theorem Formalism.L2.Col.GSD.mem_intOf (N : S.D → Submodule (𝓞 K) S.V) (φ : S.EqFun) :
    φ ∈ S.intOf N ↔ ∀ d, (φ : S.D → S.V) d ∈ N d := by sorry
