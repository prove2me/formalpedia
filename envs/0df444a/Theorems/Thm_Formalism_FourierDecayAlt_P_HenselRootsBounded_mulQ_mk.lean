-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_mulQ_mk
-- name    : Formalism.FourierDecayAlt.P.HenselRootsBounded.mulQ_mk
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:09:28.827801+00:00
-- url     : https://prove2.me/theorems/fec80d05-6d7e-4378-a937-0129742d71f8
-- title:
--   Hensel Roots Bounded: mul Q mk
-- statement:
--   The Hensel Roots Bounded construction uses the mul Q mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L461-L463
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HenselRootsBounded.lean#L461-L463

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
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.HenselRootsBounded.mulQ_mk (R : Subring K) (lam : Kˣ) (h1 : (lam : K) ∈ R) (h2 : ((lam⁻¹ : Kˣ) : K) ∈ R)
    (x : K) : mulQ R lam h1 h2 (x : K ⧸ R.toAddSubgroup) =
      (((lam : K) * x : K) : K ⧸ R.toAddSubgroup) := by sorry
