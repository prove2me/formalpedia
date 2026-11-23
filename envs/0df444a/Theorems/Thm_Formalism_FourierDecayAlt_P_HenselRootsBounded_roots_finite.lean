-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_roots_finite
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.roots_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:20.953937+00:00
-- url     : https://prove2.me/theorems/b26427f8-8796-4ed4-bc9b-4bec8ddfe6b0
-- title:
--   Hensel Roots Bounded: roots finite
-- statement:
--   The Hensel Roots Bounded construction uses the roots finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L359-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L359-L382

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

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.roots_finite {K : Type} [CommRing K] [IsArtinianRing K] [IsReduced K] (s : ℕ) (hs : 1 ≤ s)
    (D : Kˣ) : {z : Kˣ | z ^ s = D}.Finite := by sorry
