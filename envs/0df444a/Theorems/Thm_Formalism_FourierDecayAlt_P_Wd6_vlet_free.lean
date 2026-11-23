-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_vlet_free
-- name    : Formalism.FourierDecayAlt.P.Wd6.vlet_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:54.5538+00:00
-- url     : https://prove2.me/theorems/f420d2f5-e442-40fc-beb9-680b771e5737
-- title:
--   Wd6: vlet free
-- statement:
--   The Wd6 construction uses the vlet free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L333-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L333-L334

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd6
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd6.vlet_free (σ : Site A) (l : Letter K S) {a : S} (h : a ≠ l.intersection_update_fsHerm_neg_one) : FreeOf a (vlet σ l) := by sorry
