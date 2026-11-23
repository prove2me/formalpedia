-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x5_roots_finite_domain
-- name    : Formalism.FourierDecayAlt.P.A6x5.roots_finite_domain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:51:08.052797+00:00
-- url     : https://prove2.me/theorems/9f4c4acd-4610-4a44-ad48-40a345b1cbc4
-- title:
--   A6x5: roots finite domain
-- statement:
--   The A6x5 construction uses the roots finite domain property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EqZeroOfIdealCompact.lean#L7-L13

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EqZeroOfIdealCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.DoubleCosetMeasures Matrix Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x5

theorem Formalism.FourierDecayAlt.P.A6x5.roots_finite_domain {F : Type} [CommRing F] [IsDomain F] (s : ℕ) (hs : 1 ≤ s) (d : F) :
    {x : F | x ^ s = d}.Finite := by sorry
