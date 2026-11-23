-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_eq_zero_of_ideal_compact
-- name    : Formalism.FourierDecayAlt.P.A6x5.eq_zero_of_ideal_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:40.292509+00:00
-- url     : https://prove2.me/theorems/e44dc92b-c1e2-4a8c-988b-75fa78041350
-- title:
--   A6x5: eq zero of ideal compact
-- statement:
--   The A6x5 construction uses the eq zero of ideal compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L52-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L52-L81

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.A6x5.eq_zero_of_ideal_compact [T2Space K] [IsReduced K] (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (C : Set K) (hC : IsCompact C) (i : K) (hi : ∀ a : K, a * i ∈ C) : i = 0 := by sorry
