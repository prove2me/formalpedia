-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_compact_mul_small
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.compact_mul_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:41.078822+00:00
-- url     : https://prove2.me/theorems/284a5d16-f29c-433f-9358-3ae11fac5f76
-- title:
--   Germ Sum Lattices: compact mul small
-- statement:
--   The Germ Sum Lattices construction uses the compact mul small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L27-L38

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.GermSumLattices.compact_mul_small {C : Set K} (hC : IsCompact C) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ E ∈ 𝓝 (0 : K), ∀ z ∈ C, ∀ e ∈ E, z * e ∈ W := by sorry
