-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_small_add
-- name    : Formalism.FourierDecayAlt.P.A6x8.small_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:46.113048+00:00
-- url     : https://prove2.me/theorems/3419aed5-eef8-4437-8b4c-11fe980fb9fd
-- title:
--   A6x8: small add
-- statement:
--   The A6x8 construction uses the small add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L52-L60

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.A6x8.small_add {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ W ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ w ∈ W, z + w ∈ Om := by sorry
