-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_lie_Q
-- name    : Formalism.FourierDecayAlt.P.Ux4.lie_Q
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:27:50.837523+00:00
-- url     : https://prove2.me/theorems/e7a60dbf-820e-49bd-a248-abf96965490d
-- title:
--   Ux4: lie Q
-- statement:
--   The Ux4 construction uses the lie Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L323-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L323-L331

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux4
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux4.lie_Q (Q : Matrix (Fin j) (Fin j) ℂ) :
    B.inLie k (j + ρ) (blk3 (k := k) (ρ := ρ) Q 0 0 0 0 0 0 0 (-(G.wMat j * Qᴴ * G.wMat j))) := by sorry
