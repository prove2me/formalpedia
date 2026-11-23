-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_bounded
-- name    : Formalism.FourierDecayAlt.P.A6x4.bounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:39.139097+00:00
-- url     : https://prove2.me/theorems/bec318c4-1272-489f-97c5-c9bef9ca00b6
-- title:
--   A6x4: bounded
-- statement:
--   The A6x4 construction uses the bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L294-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L294-L310

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

theorem Formalism.FourierDecayAlt.P.A6x4.bounded (hD : LocalDatum K R ψ) {p : K} (hp : p ∈ R)
    (hex : ∀ x : K, ∃ m : ℕ, p ^ m * x ∈ R) {C : Set K} (hC : IsCompact C) :
    ∃ m : ℕ, ∀ z ∈ C, p ^ m * z ∈ R := by sorry
