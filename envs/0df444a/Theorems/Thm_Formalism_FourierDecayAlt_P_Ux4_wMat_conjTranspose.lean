-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_wMat_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Ux4.wMat_conjTranspose
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T15:19:39.185804+00:00
-- url     : https://prove2.me/theorems/aa52df0e-8fd5-41d5-a41b-7853095d673d
-- title:
--   Ux4: w Mat conj Transpose
-- statement:
--   The Ux4 construction uses the w Mat conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L123-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L123-L133

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

theorem Formalism.FourierDecayAlt.P.Ux4.wMat_conjTranspose (d : ℕ) : (G.wMat d)ᴴ = G.wMat d := by sorry
