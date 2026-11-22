-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mulU
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.mulU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:47.383813+00:00
-- url     : https://prove2.me/theorems/c3796426-49f2-4a04-b8ae-a60de90d8ca3
-- title:
--   Hensel Roots Bounded: mul U
-- statement:
--   The Hensel Roots Bounded construction uses the mul U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L243-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L243-L249

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.mulU (h : Ctx K R ϖ) {n : ℤ} (hn : 0 ≤ n) {x y : K} (hx : x - 1 ∈ Pk R ϖ n)
    (hy : y - 1 ∈ Pk R ϖ n) : x * y - 1 ∈ Pk R ϖ n := by sorry
