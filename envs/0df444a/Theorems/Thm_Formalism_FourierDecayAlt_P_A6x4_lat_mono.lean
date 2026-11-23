-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_lat_mono
-- name    : Formalism.FourierDecayAlt.P.A6x4.lat_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:40.552731+00:00
-- url     : https://prove2.me/theorems/5a3ddf32-08e3-4d09-9f9b-1bd75eb50343
-- title:
--   A6x4: lat mono
-- statement:
--   The A6x4 construction uses the lat mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L197-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ModulusLocallyConstant.lean#L197-L205

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

theorem Formalism.FourierDecayAlt.P.A6x4.lat_mono {p q : K} (hpq : p * q = 1) (hp : p ∈ R) {m m' : ℕ} (h : m ≤ m') {x : K}
    (hx : q ^ m' * x ∈ R) : q ^ m * x ∈ R := by sorry
