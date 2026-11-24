-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_hpk_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Ux4.hpk_conjTranspose
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:53:14.239165+00:00
-- url     : https://prove2.me/theorems/b6c738b0-e06f-4307-9b92-24476c4579bc
-- title:
--   Ux4: hpk conj Transpose
-- statement:
--   The Ux4 construction uses the hpk conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L135-L144

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

theorem Formalism.FourierDecayAlt.P.Ux4.hpk_conjTranspose (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by sorry
