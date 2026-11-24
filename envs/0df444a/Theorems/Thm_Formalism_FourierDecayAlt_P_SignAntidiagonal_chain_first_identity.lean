-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SignAntidiagonal_chain_first_identity
-- name    : Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_identity
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:19:56.443175+00:00
-- url     : https://prove2.me/theorems/89234f23-9f30-4d3b-98be-76bf8dd0e187
-- title:
--   Sign Antidiagonal: chain first identity
-- statement:
--   The Sign Antidiagonal construction uses the chain first identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainFirstIdentity.lean#L16-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChainFirstIdentity.lean#L16-L113

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourthExpansionIdentity
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_QuantumDetHighestWeightHolds
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainFirstIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SignAntidiagonal
open Formalism.FourierDecayAlt.C3 Formalism.REAL Formalism.QuantumDeterminants

theorem Formalism.FourierDecayAlt.P.SignAntidiagonal.chain_first_identity : LastColumnChain := by sorry
