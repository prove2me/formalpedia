-- Prove2me | Theorems.Thm_Formalism_L2_Th1_C_USideA_intPS_sum
-- name    : Formalism.L2.Th1.C.USideA.intPS_sum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:57:58.870443+00:00
-- url     : https://prove2.me/theorems/9a8c8b62-01c0-4ee9-b246-73ac0bdc7a6a
-- title:
--   USide A: int PS sum
-- statement:
--   The USide A construction uses the int PS sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L43-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/BinomialSeriesCoefficients/USideA.lean#L43-L46

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
variable {K : Type} [Field K] {R : Subring K}

theorem Formalism.L2.Th1.C.USideA.intPS_sum {ι : Type} (s : Finset ι) {F : ι → PowerSeries K} (hF : ∀ i ∈ s, IntPS R (F i)) :
    IntPS R (∑ i ∈ s, F i) := by sorry
