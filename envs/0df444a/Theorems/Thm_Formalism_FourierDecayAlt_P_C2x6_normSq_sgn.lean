-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_normSq_sgn
-- name    : Formalism.FourierDecayAlt.P.C2x6.normSq_sgn
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:13:07.82899+00:00
-- url     : https://prove2.me/theorems/a5d3604c-718a-403b-9e0e-f785fad7cef5
-- title:
--   C2x6: norm Sq sgn
-- statement:
--   The C2x6 construction uses the norm Sq sgn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MajorantEstimate.lean#L67-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MajorantEstimate.lean#L67-L69

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFlagVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MajorantEstimate
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
open Formalism.FourierDecayAlt.P.C2x6
open C2x5
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x6.normSq_sgn (i : Fin (2 * r + k + 1)) : Complex.normSq (GBasic.sgn k r i) = 1 := by sorry
