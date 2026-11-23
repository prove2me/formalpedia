-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_small_scale
-- name    : Formalism.FourierDecayAlt.P.A6x8.small_scale
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:18.253392+00:00
-- url     : https://prove2.me/theorems/10c0e472-f370-428f-9a10-75e637ffe44a
-- title:
--   A6x8: small scale
-- statement:
--   The A6x8 construction uses the small scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L62-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L62-L69

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

theorem Formalism.FourierDecayAlt.P.A6x8.small_scale {Om : Set K} (hC : IsCompact Om) (hO : IsOpen Om) :
    ∃ E ∈ 𝓝 (0 : K), ∀ z ∈ Om, ∀ κ : K, κ - 1 ∈ E → κ * z ∈ Om := by sorry
