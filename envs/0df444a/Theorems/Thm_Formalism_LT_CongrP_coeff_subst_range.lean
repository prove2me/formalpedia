-- Prove2me | Theorems.Thm_Formalism_LT_CongrP_coeff_subst_range
-- name    : Formalism.LT.CongrP.coeff_subst_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:57:07.485049+00:00
-- url     : https://prove2.me/theorems/9bb77826-e30d-431a-9ebc-3929261766d4
-- title:
--   Congr P: coeff subst range
-- statement:
--   The Congr P construction uses the coeff subst range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L18-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/TorsionNormIteration/InverseIntegralClasses/CoeffSubstAddCMulXPow.lean#L18-L29

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_CoeffSubstAddCMulXPow
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
open Formalism Formalism.LT Formalism.LT.CongrP
open Formalism.G
variable {R : Type*} [CommRing R]

theorem Formalism.LT.CongrP.coeff_subst_range (f a : PowerSeries R) (ha : constantCoeff a = 0) (N : ℕ) :
    coeff N (f.subst a) = ∑ n ∈ Finset.range (N + 1), coeff n f * coeff N (a ^ n) := by sorry
