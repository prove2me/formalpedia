-- Prove2me | Theorems.Thm_Formalism_LT_LTL_near_one_subst_X_coeff_one_smul_X
-- name    : Formalism.LT.LTL.near_one_subst_X_coeff_one_smul_X
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:57.432805+00:00
-- url     : https://prove2.me/theorems/7510d12b-fc2f-4b10-94be-4957903e3a1c
-- title:
--   LTL: near one subst X coeff one smul X
-- statement:
--   The LTL construction uses the near one subst X coeff one smul X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L118-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/LTLemma.lean#L118-L133

import Definitions.Def_Formalism_TorsionNormIteration_LTLemma
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_InvInt
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_MemSpanOfNormLe
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_LTLemma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.LT Formalism.LT.LTL
open Formalism.G Formalism.G.LogCR Formalism.LT.InvIntP
variable {K : Type u} [NormedField K] {ι : Type*}

theorem Formalism.LT.LTL.near_one_subst_X_coeff_one_smul_X (f : PowerSeries K) (h0 : constantCoeff f = 0) (i : ι) :
    Near 1 (f.subst (MvPowerSeries.X i : MvPowerSeries ι K))
      (((fun _ : ι => coeff 1 f) • (MvPowerSeries.X : ι → MvPowerSeries ι K)) i) := by sorry
