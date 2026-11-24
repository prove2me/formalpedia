-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_mulVec_col
-- name    : Formalism.FourierDecayAlt.Q.Adapted.mulVec_col
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:23:55.271804+00:00
-- url     : https://prove2.me/theorems/4c3489e5-f889-457a-8de8-b57882a41e22
-- title:
--   Adapted: mul Vec col
-- statement:
--   The Adapted construction uses the mul Vec col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdaptedCharacterForm/SecondCapelliMinorStandardBasis.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdaptedCharacterForm/SecondCapelliMinorStandardBasis.lean#L10-L15

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.Adapted
open Formalism.REAL

theorem Formalism.FourierDecayAlt.Q.Adapted.mulVec_col {n : ℕ} (P Q : Matrix (Fin n) (Fin n) ℂ) (h : Q * P = 1) (k : Fin n) :
    (Q *ᵥ fun p => P p k) = Pi.single k 1 := by sorry
