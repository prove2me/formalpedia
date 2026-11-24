-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_iSet_card
-- name    : Formalism.FourierDecayAlt.P.c2x3_iSet_card
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:14:39.946029+00:00
-- url     : https://prove2.me/theorems/e60a4a20-e6a5-49e1-a761-5b82f2f2ae0c
-- title:
--   P: c2x3 i Set card
-- statement:
--   The P construction uses the c2x3 i Set card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L65-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StabilizerAntidiagonalExact.lean#L65-L67

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

theorem Formalism.FourierDecayAlt.P.c2x3_iSet_card {m a : ℕ} (h : a ≤ m) : (C2.iSet m a).card = a := by sorry
