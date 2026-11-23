-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_pow_small
-- name    : Formalism.FourierDecayAlt.P.A6x5.pow_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:33.225631+00:00
-- url     : https://prove2.me/theorems/d274fe71-3e56-47bd-b4bc-af9232822184
-- title:
--   A6x5: pow small
-- statement:
--   The A6x5 construction uses the pow small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L98-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L98-L125

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
variable {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x5.pow_small (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R)
    (V : Set K) (hV : V ∈ 𝓝 (0 : K)) : ∃ N : ℕ, ∀ r ∈ R, (ϖ : K) ^ N * r ∈ V := by sorry
