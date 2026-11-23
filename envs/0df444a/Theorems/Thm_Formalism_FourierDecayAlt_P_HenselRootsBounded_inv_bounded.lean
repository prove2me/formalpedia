-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_inv_bounded
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.inv_bounded
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:15.893691+00:00
-- url     : https://prove2.me/theorems/1c057135-6c37-4355-86b0-4b081b095148
-- title:
--   Hensel Roots Bounded: inv bounded
-- statement:
--   The Hensel Roots Bounded construction uses the inv bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L313-L349
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L313-L349

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.inv_bounded (h : Ctx K R ϖ) {Om : Set K} (hOm : IsCompact Om) (hu : ∀ z ∈ Om, IsUnit z) :
    ∃ b : ℕ, ∀ z ∈ Om, ∀ zi : K, z * zi = 1 → zi ∈ Pk R ϖ (-(b : ℤ)) := by sorry
