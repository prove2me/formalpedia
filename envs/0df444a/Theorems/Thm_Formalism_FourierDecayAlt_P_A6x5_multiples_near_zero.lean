-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_multiples_near_zero
-- name    : Formalism.FourierDecayAlt.P.A6x5.multiples_near_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:35.916258+00:00
-- url     : https://prove2.me/theorems/872a71f1-9341-469f-8306-59947fc1bee3
-- title:
--   A6x5: multiples near zero
-- statement:
--   The A6x5 construction uses the multiples near zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L30-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L30-L50

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

theorem Formalism.FourierDecayAlt.P.A6x5.multiples_near_zero (C : Set K) (hC : IsCompact C) (i : K) (hi : ∀ a : K, a * i ∈ C)
    (W : Set K) (hW : W ∈ 𝓝 (0 : K)) : ∃ k : ℕ, ((k + 1 : ℕ) : K) * i ∈ W := by sorry
