-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_approx_zero
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.approx_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:46:39.726683+00:00
-- url     : https://prove2.me/theorems/da101053-7716-43eb-80f7-2c3d4263195d
-- title:
--   Hensel Roots Bounded: approx zero
-- statement:
--   The Hensel Roots Bounded construction uses the approx zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L162-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L162-L175

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.approx_zero (h : Ctx K R ϖ) {C : Set K} (hC : IsCompact C) {f : K → K} (hf : Continuous f)
    (hap : ∀ k : ℕ, ∃ w ∈ C, f w ∈ Pk R ϖ k) : ∃ w ∈ C, f w = 0 := by sorry
