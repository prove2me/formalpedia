-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_form_sum_orth
-- name    : Formalism.L2.SG.Pf.GluingBases.form_sum_orth
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:28.900803+00:00
-- url     : https://prove2.me/theorems/6a182d7c-fc98-5bfb-807c-49f96f7a613a
-- title:
--   Gluing Bases: form sum orth
-- statement:
--   The Gluing Bases construction uses the form sum orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/FamilyDualHolds.lean#L16-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/FamilyDualHolds.lean#L16-L21

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_LinearIndependentOrth
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SmulMemLocFOfSP
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_GlueInlInl
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_FamilyDualHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.GluingBases.form_sum_orth {ι' : Type} [Fintype ι'] [DecidableEq ι'] (h : V →ₗ⋆[K] V →ₗ[K] K) (v : ι' → V)
    (hvo : ∀ i k, i ≠ k → h (v i) (v k) = 0) (i : ι') (x : ι' → K) :
    h (v i) (∑ k, x k • v k) = x i * h (v i) (v i) := by sorry
