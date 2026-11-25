-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_NcReal_JX_CovB_IdxK_relIndex_eq_card
-- name    : Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_eq_card
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:16:43.826253+00:00
-- url     : https://prove2.me/theorems/aec8beee-2c18-4dfd-bfe1-c8fda093a54d
-- title:
--   Idx K: rel Index eq card
-- statement:
--   The Idx K construction uses the rel Index eq card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L320-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/CovolIdxK.lean#L320-L322

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
variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [NoZeroSMulDivisors (𝓞 K) M]

theorem Formalism.L2.SG.Pf.NcReal.JX.CovB.IdxK.relIndex_eq_card (I : Ideal (𝓞 K)) (N : Submodule (𝓞 K) M) :
    (I • N).toAddSubgroup.relIndex N.toAddSubgroup = Nat.card (N ⧸ I • (⊤ : Submodule (𝓞 K) N)) := by sorry
