-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_Adapted_coefA
-- name    : Formalism.FourierDecayAlt.Q.Adapted.coefA
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T16:44:08.511564+00:00
-- url     : https://prove2.me/theorems/9859441d-0033-4303-91a5-d549449a0f5d
-- title:
--   Adapted: coef A
-- statement:
--   The Adapted construction uses the coef A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdaptedCharacterForm/SecondCapelliMinorStandardBasis.lean#L29-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/AdaptedCharacterForm/SecondCapelliMinorStandardBasis.lean#L29-L36

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

theorem Formalism.FourierDecayAlt.Q.Adapted.coefA {n : ℕ} (j j' : Fin (n + 2)) (h : j < j') :
    (Pi.single 0 1 : Fin (n + 2) → ℂ) j * (Pi.single 1 1 : Fin (n + 2) → ℂ) j' -
      (Pi.single 0 1 : Fin (n + 2) → ℂ) j' * (Pi.single 1 1 : Fin (n + 2) → ℂ) j =
      if j = 0 ∧ j' = 1 then 1 else 0 := by sorry
