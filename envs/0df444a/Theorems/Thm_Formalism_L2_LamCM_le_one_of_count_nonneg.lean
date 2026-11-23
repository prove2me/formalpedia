-- Prove2me | Theorems.Thm_Formalism_L2_LamCM_le_one_of_count_nonneg
-- name    : Formalism.L2.LamCM.le_one_of_count_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:07.885796+00:00
-- url     : https://prove2.me/theorems/44bcde9e-83b4-4cf3-a441-d48ff5fa3886
-- title:
--   Lam CM: le one of count nonneg
-- statement:
--   The Lam CM construction uses the le one of count nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L64-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CMDeterminantIdeals/CMIdealValuations/OneLeAbsNormOfLeOne.lean#L64-L70

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_OneLeAbsNormOfLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem Formalism.L2.LamCM.le_one_of_count_nonneg {J : FractionalIdeal (𝓞 K)⁰ K} (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), 0 ≤ FractionalIdeal.count K v J) : J ≤ 1 := by sorry
