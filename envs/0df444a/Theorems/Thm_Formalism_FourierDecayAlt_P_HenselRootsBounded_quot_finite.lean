-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_quot_finite
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.quot_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:26.972876+00:00
-- url     : https://prove2.me/theorems/5644eabc-6b13-435f-b169-f0def4754191
-- title:
--   Hensel Roots Bounded: quot finite
-- statement:
--   The Hensel Roots Bounded construction uses the quot finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L597-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L597-L600

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.quot_finite (h : Ctx K R ϖ) (k l : ℤ) :
    Finite (Pk R ϖ k ⧸ (Pk R ϖ l).addSubgroupOf (Pk R ϖ k)) := by sorry
