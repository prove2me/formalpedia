-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_wSet_card
-- name    : Formalism.FourierDecayAlt.P.c2x3_wSet_card
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:16:12.68698+00:00
-- url     : https://prove2.me/theorems/e5950790-3cbc-4eda-b7b2-46f4295a76b1
-- title:
--   P: c2x3 w Set card
-- statement:
--   The P construction uses the c2x3 w Set card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L69-L71

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open C2x2

theorem Formalism.FourierDecayAlt.P.c2x3_wSet_card {m a : ℕ} (w : Equiv.Perm (Fin m)) (h : a ≤ m) : (C2.wSet w a).card = a := by sorry
