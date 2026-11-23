-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_unitBox_isOpen
-- name    : Formalism.FourierDecayAlt.P.A6x5.unitBox_isOpen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:05.357963+00:00
-- url     : https://prove2.me/theorems/d79370eb-3b86-4dfe-920c-bee89fb7c7fe
-- title:
--   A6x5: unit Box is Open
-- statement:
--   The A6x5 construction uses the unit Box is Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L223-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L223-L249

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

theorem Formalism.FourierDecayAlt.P.A6x5.unitBox_isOpen (hD : LocalDatum K R ψ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K))
    (ϖ : Kˣ) (hϖR : (ϖ : K) ∈ R) (hϖ : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R) (j : ℕ) :
    IsOpen (unitBox R ϖ j) := by sorry
