-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_root
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.root
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:18.267857+00:00
-- url     : https://prove2.me/theorems/59fc36d9-3d53-4f7e-a046-b984c8d4bb08
-- title:
--   Adic: root
-- statement:
--   The Adic construction uses the root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L185-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L185-L210

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.root (h : Adic R ϖ) (s : ℕ) {c : K} (hc : c ∈ I R (ϖ : K)) {b : K}
    (hb : Near R ((s : K) ^ 2 * c) b) : ∃ κ, Near R ((s : K) * c) κ ∧ κ ^ s = b := by sorry
