-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideA_subst_sum
-- name    : Formalism.L2.Th1.C.USideA.subst_sum
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:47:38.545108+00:00
-- url     : https://prove2.me/theorems/90c20dca-ae71-55ed-9557-806e4b5d2069
-- title:
--   USide A: subst sum
-- statement:
--   The USide A construction uses the subst sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L126-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L126-L129

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_DegreeLeOfMemAntidiagonal
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_BinomialSeriesCoefficients_USideA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.C
open Formalism.L2.Th1.C.USideA
variable {K : Type} [Field K]

theorem Formalism.L2.Th1.C.USideA.subst_sum {ι : Type} {a : PowerSeries K} (ha : PowerSeries.HasSubst a) (s : Finset ι)
    (F : ι → PowerSeries K) :
    PowerSeries.subst a (∑ i ∈ s, F i) = ∑ i ∈ s, PowerSeries.subst a (F i) := by sorry
