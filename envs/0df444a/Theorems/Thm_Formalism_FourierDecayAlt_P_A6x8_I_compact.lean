-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_I_compact
-- name    : Formalism.FourierDecayAlt.P.A6x8.I_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:54:26.607842+00:00
-- url     : https://prove2.me/theorems/47164157-2a89-4703-b67c-6e59d3ef7045
-- title:
--   A6x8: I compact
-- statement:
--   The A6x8 construction uses the I compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L73-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L73-L79

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

theorem Formalism.FourierDecayAlt.P.A6x8.I_compact {R : Subring K} (hc : IsCompact (R : Set K)) (a : K) : IsCompact (I R a) := by sorry
