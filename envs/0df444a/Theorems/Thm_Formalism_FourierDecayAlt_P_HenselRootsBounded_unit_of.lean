-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_unit_of
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.unit_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:27.038243+00:00
-- url     : https://prove2.me/theorems/5d72a91c-b9cd-4ce8-918e-9e46e4ac694b
-- title:
--   Hensel Roots Bounded: unit of
-- statement:
--   The Hensel Roots Bounded construction uses the unit of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L592-L595
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L592-L595

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.unit_of (h : Ctx K R ϖ) {k : ℤ} (hk : 1 ≤ k) {w : K} (hw : w ∈ Pk R ϖ k) :
    ∃ (ω : Kˣ) (w' : K), (ω : K) = 1 + w ∧ ((ω⁻¹ : Kˣ) : K) = 1 + w' ∧ w' ∈ Pk R ϖ k := by sorry
