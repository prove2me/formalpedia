-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_dualSpan_true_hc
-- name    : Formalism.FourierDecayAlt.P.dualSpan_true_hc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:31:12.009131+00:00
-- url     : https://prove2.me/theorems/7e0b8539-fabd-5eec-a541-de92edf3e56e
-- title:
--   P: dual Span true hc
-- statement:
--   The P construction uses the dual Span true hc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L331-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CharacterOrthogonalityDual.lean#L331-L335

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open A5x3

theorem Formalism.FourierDecayAlt.P.dualSpan_true_hc : Formalism.FourierDecayAlt.A5.DualSpan := by sorry
