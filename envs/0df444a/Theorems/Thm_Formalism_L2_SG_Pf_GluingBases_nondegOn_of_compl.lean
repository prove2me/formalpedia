-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_GluingBases_nondegOn_of_compl
-- name    : Formalism.L2.SG.Pf.GluingBases.nondegOn_of_compl
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:48:30.980597+00:00
-- url     : https://prove2.me/theorems/38fcc7f0-70ed-5d43-b126-0f2b26877bcf
-- title:
--   Gluing Bases: nondeg On of compl
-- statement:
--   The Gluing Bases construction uses the nondeg On of compl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NondegOnOfCompl.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/NondegOnOfCompl.lean#L51-L61

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_IsLatticeSpanO
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_NondegOnOfCompl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.GluingBases
open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU Formalism.HermitianLattices.Ext.L3.integralBasisSpans
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]

theorem Formalism.L2.SG.Pf.GluingBases.nondegOn_of_compl {h : V →ₗ⋆[K] V →ₗ[K] K} (hnd : Nondeg h) {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) : NondegOn h U := by sorry
