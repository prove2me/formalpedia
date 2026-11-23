-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_root_bounded
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.root_bounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:12:52.194888+00:00
-- url     : https://prove2.me/theorems/3a37c9db-35c2-4ec7-adad-6504aceb1e05
-- title:
--   Adic: root bounded
-- statement:
--   The Adic construction uses the root bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L223-L253
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L223-L253

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.root_bounded (h : Adic R ϖ) [IsReduced K] (s : ℕ) (hs : 1 ≤ s) :
    ∃ n0 : ℕ, ∀ v : K, v ^ s ∈ R → (ϖ : K) ^ n0 * v ∈ R := by sorry
