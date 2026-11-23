-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_RealPowerIdentities_rpow_half_mul_pow_triangle
-- name    : Formalism.FourierDecayAlt.P.RealPowerIdentities.rpow_half_mul_pow_triangle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:35:37.996354+00:00
-- url     : https://prove2.me/theorems/05538aa4-fd66-4165-aa59-075773e993e0
-- title:
--   Real Power Identities: rpow half mul pow triangle
-- statement:
--   The Real Power Identities construction uses the rpow half mul pow triangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealPowerIdentities.lean#L20-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RealPowerIdentities.lean#L20-L29

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

theorem Formalism.FourierDecayAlt.P.RealPowerIdentities.rpow_half_mul_pow_triangle {Z : ℝ} (hZ : 0 < Z) {m : ℕ} (hm : 1 ≤ m) :
    Z ^ ((m : ℝ) / 2) * Z ^ (m * (m - 1) / 2) = Z ^ ((m : ℝ) ^ 2 / 2) := by sorry
