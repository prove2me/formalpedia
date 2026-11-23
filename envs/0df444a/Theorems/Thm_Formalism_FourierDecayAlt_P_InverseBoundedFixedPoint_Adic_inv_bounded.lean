-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_inv_bounded
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.inv_bounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:10:00.871308+00:00
-- url     : https://prove2.me/theorems/f48f2368-22d8-49c3-ba94-2241769c5ea0
-- title:
--   Adic: inv bounded
-- statement:
--   The Adic construction uses the inv bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L146-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L146-L175

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.inv_bounded (h : Adic R ϖ) {Om : Set K} (hC : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ M : ℕ, ∀ z ∈ Om, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R := by sorry
