-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_bT_free
-- name    : Formalism.FourierDecayAlt.P.Wd6.bT_free
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:00.200679+00:00
-- url     : https://prove2.me/theorems/1b80280c-88ab-4b7f-8e1f-712de7382173
-- title:
--   Wd6: b T free
-- statement:
--   The Wd6 construction uses the b T free property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L336-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L336-L342

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

theorem Formalism.FourierDecayAlt.P.Wd6.bT_free (σ : Site A) (w : List (Letter K S)) {a : S} (h : a ∉ w.map Letter.intersection_update_fsHerm_neg_one) :
    FreeOf a (bT σ w) := by sorry
