-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealPowerIdentities_inv_pow_triangle_mul_rpow_half
-- name    : Formalism.FourierDecayAlt.P.RealPowerIdentities.inv_pow_triangle_mul_rpow_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:50.757915+00:00
-- url     : https://prove2.me/theorems/a7735cee-d31b-463f-bc3b-2bf14fa1d0f6
-- title:
--   Real Power Identities: inv pow triangle mul rpow half
-- statement:
--   The Real Power Identities construction uses the inv pow triangle mul rpow half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealPowerIdentities.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealPowerIdentities.lean#L9-L18

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RealPowerIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.RealPowerIdentities

theorem Formalism.FourierDecayAlt.P.RealPowerIdentities.inv_pow_triangle_mul_rpow_half {T : ℝ} (hT : 0 < T) (m : ℕ) :
    (T ^ (m * (m + 1) / 2))⁻¹ * T ^ ((m : ℝ) / 2) = T ^ (-((m : ℝ) ^ 2) / 2) := by sorry
