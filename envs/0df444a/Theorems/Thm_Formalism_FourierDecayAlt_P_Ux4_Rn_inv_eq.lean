-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux4_Rn_inv_eq
-- name    : Formalism.FourierDecayAlt.P.Ux4.Rn_inv_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:22:38.857566+00:00
-- url     : https://prove2.me/theorems/5427dfc7-0a25-4fcc-9735-9196b1963369
-- title:
--   Ux4: Rn inv eq
-- statement:
--   The Ux4 construction uses the Rn inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L185-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DirectionsInParabolic.lean#L185-L185

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

theorem Formalism.FourierDecayAlt.P.Ux4.Rn_inv_eq (x : RC k j ρ) : (Rn k j ρ x)⁻¹ = RnInv x := by sorry
