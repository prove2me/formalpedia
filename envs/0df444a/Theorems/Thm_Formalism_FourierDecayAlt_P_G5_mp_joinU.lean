-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_mp_joinU
-- name    : Formalism.FourierDecayAlt.P.G5.mp_joinU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:54:16.533204+00:00
-- url     : https://prove2.me/theorems/633bba6e-f864-4add-9b0f-59a47498a909
-- title:
--   G5: mp join U
-- statement:
--   The G5 construction uses the mp join U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L291-L304
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L291-L304

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.mp_joinU (β : ℂ) (n : ℕ) :
    MeasurePreserving (joinU : (UT n → ℂ) × (Fin n → ℂ) → UT (n + 1) → ℂ)
      ((muPi β (UT n)).prod (muPi β (Fin n))) (muPi β (UT (n + 1))) := by sorry
