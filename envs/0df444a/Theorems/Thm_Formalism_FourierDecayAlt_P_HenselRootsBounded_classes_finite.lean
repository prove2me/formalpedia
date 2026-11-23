-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_classes_finite
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.classes_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:11.216359+00:00
-- url     : https://prove2.me/theorems/cfdb264e-beff-4364-8b2c-436b7c97b659
-- title:
--   Hensel Roots Bounded: classes finite
-- statement:
--   The Hensel Roots Bounded construction uses the classes finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L351-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L351-L355

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.classes_finite (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) :
    {x : K ⧸ R.toAddSubgroup | ∃ c ∈ C, ((c : K) : K ⧸ R.toAddSubgroup) = x}.Finite := by sorry
