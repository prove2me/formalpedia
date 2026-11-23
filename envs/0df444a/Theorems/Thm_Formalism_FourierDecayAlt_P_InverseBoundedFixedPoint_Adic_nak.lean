-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_nak
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.nak
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:56.151193+00:00
-- url     : https://prove2.me/theorems/85111297-61ad-4c6b-819b-0e83589a8a97
-- title:
--   Adic: nak
-- statement:
--   The Adic construction uses the nak property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L323-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L323-L342

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

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.nak (h : Adic R ϖ) {ι : Type} [Finite ι] (d : ι → K) (Λ : Submodule R K)
    (hd : ∀ Λ' : Submodule R K, (∀ i, d i ∈ Λ') → ∀ i, ∃ l ∈ Λ, ∃ l' ∈ Λ', d i = l + (ϖ : K) * l') :
    ∀ i, d i ∈ Λ := by sorry
