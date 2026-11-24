-- Prove2me | Theorems.Thm_Formalism_QuantumDeterminants_integrable_of_on
-- name    : Formalism.QuantumDeterminants.integrable_of_on
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:20:02.174582+00:00
-- url     : https://prove2.me/theorems/877e7051-99d5-4eb2-81f3-4c60ce201a43
-- title:
--   Quantum Determinants: integrable of on
-- statement:
--   The Quantum Determinants construction uses the integrable of on property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/FormalDegreeRatio/AdjointFunctionalHolds.lean#L121-L126

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementWR
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_AdjointFunctionalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open MeasureTheory
noncomputable section
open Formalism Formalism.QuantumDeterminants
variable {m : ℕ}

theorem Formalism.QuantumDeterminants.integrable_of_on {φ h : (Fin m → ℂ) → ℂ} (hc : ContinuousOn φ (OmX m))
    (hs : tsupport φ ⊆ tsupport h) (hK : HasCompactSupport h) (hΩ : tsupport h ⊆ OmX m) :
    Integrable φ := by sorry
