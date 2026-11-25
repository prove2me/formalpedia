-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_smul_toAddSubgroup
-- name    : Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.smul_toAddSubgroup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:17:02.419462+00:00
-- url     : https://prove2.me/theorems/e621f1a6-95c7-4340-be56-e588c02cc047
-- title:
--   Idx K: smul to Add Subgroup
-- statement:
--   The Idx K construction uses the smul to Add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L165-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L165-L172

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_CovolIdxK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.NcReal Formalism.L2.SG.Pf.NcReal.JX Formalism.L2.SG.Pf.NcReal.JX.CovB Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK
variable {K : Type} [Field K] [NumberField K]
open scoped Pointwise
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]

theorem Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.smul_toAddSubgroup (π : 𝓞 K) (N : Submodule (𝓞 K) M) :
    (Ideal.span {π} • N).toAddSubgroup = N.toAddSubgroup.map (DistribSMul.toAddMonoidHom M π) := by sorry
