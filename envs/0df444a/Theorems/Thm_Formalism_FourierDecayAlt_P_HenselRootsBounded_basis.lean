-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_basis
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:44.628806+00:00
-- url     : https://prove2.me/theorems/169153eb-2c34-4cc4-8c37-909f0f0d355f
-- title:
--   Hensel Roots Bounded: basis
-- statement:
--   The Hensel Roots Bounded construction uses the basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L177-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L177-L194

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.basis (h : Ctx K R ϖ) {W : Set K} (hW : W ∈ 𝓝 (0 : K)) :
    ∃ k : ℕ, ∀ x ∈ Pk R ϖ k, x ∈ W := by sorry
