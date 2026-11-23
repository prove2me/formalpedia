-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_conj_identity
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.conj_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:55.95244+00:00
-- url     : https://prove2.me/theorems/0c5264ec-0cff-42a5-9690-5488086a441d
-- title:
--   Inverse Bounded Fixed Point: conj identity
-- statement:
--   The Inverse Bounded Fixed Point construction uses the conj identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L620-L634
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L620-L634

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] {m : ℕ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.conj_identity (p : K) (Y N : Matrix (Fin m) (Fin m) K) (hs : Yᵀ = Y)
    (e : Y = N - p • (Y * HA K m * Y)) :
    (1 + (2 * p) • (HA K m * Y))ᵀ * HH K m * (1 + (2 * p) • (HA K m * Y)) =
      HH K m + (4 * ((m + 1 : ℕ) : K) * p) • N := by sorry
