-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_skewOf_conjTranspose
-- name    : Formalism.FourierDecayAlt.P.Ux4.skewOf_conjTranspose
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:28:13.683729+00:00
-- url     : https://prove2.me/theorems/acb854b2-637e-4c43-a920-a6a9883bb8d6
-- title:
--   Ux4: skew Of conj Transpose
-- statement:
--   The Ux4 construction uses the skew Of conj Transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L278-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L278-L286

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

theorem Formalism.FourierDecayAlt.P.Ux4.skewOf_conjTranspose (q : (G.UT j → ℂ) × (Fin j → ℝ)) : (skewOf q)ᴴ = -skewOf q := by sorry
