-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_dual_exists
-- name    : Formalism.FourierDecayAlt.P.A6x4.dual_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:45.484921+00:00
-- url     : https://prove2.me/theorems/8350438c-9343-4de4-ae99-c3f4cf613e28
-- title:
--   A6x4: dual exists
-- statement:
--   The A6x4 construction uses the dual exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L395-L497
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L395-L497

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.A6x4.dual_exists (hD : LocalDatum K R ψ) {a b : K} (hab : a * b = 1) (ha : a ∈ R)
    (χ : AddChar R ℂ) (hχ : ∀ r : R, (r : K) ∈ mulR R a → χ r = 1) :
    ∃ z : K, ∀ r : R, χ r = ψ (z * (r : K)) := by sorry
