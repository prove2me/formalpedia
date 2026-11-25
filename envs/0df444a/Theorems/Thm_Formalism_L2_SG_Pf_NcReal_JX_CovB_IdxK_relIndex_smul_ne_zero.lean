-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_smul_ne_zero
-- name    : Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_smul_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T07:16:37.9776+00:00
-- url     : https://prove2.me/theorems/075815e9-4c3d-5617-bf1a-3e507b02f499
-- title:
--   Idx K: rel Index smul ne zero
-- statement:
--   The Idx K construction uses the rel Index smul ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L218-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L218-L229

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

theorem Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_smul_ne_zero (N : Submodule (𝓞 K) M) (hN : N.FG) (d : 𝓞 K) (hd : d ≠ 0) :
    (Ideal.span {d} • N).toAddSubgroup.relIndex N.toAddSubgroup ≠ 0 := by sorry
