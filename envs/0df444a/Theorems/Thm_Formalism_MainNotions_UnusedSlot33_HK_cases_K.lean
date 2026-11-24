-- Prove2me | Theorems.Thm_Formalism_MainNotions_UnusedSlot33_HK_cases_K
-- name    : Formalism.MainNotions.UnusedSlot33.HK.cases_K
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:45.996498+00:00
-- url     : https://prove2.me/theorems/3bbb3c4b-e93c-436c-a83e-a57868549359
-- title:
--   HK: cases K
-- statement:
--   The HK construction uses the cases K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L225-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GlobalSchurBounds/GlobalRankLatticeProofs/EqOfLeOfAbsNormEq.lean#L225-L233

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GlobalRankLatticeProofs_EqOfLeOfAbsNormEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.UnusedSlot33 Formalism.MainNotions.UnusedSlot33.HK
open NumberField Polynomial Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
variable {R : Ranks} (H : Host R)

theorem Formalism.MainNotions.UnusedSlot33.HK.cases_K (σ : H.E ≃ₐ[ℚ] H.E) :
    (∀ x ∈ H.K, σ x = x) ∨ (∀ x ∈ H.K, σ x = H.conj x) := by sorry
