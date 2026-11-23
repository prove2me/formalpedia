-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_vlet_units
-- name    : Formalism.FourierDecayAlt.P.Wd6.vlet_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:07.716479+00:00
-- url     : https://prove2.me/theorems/1cdaecc3-d31e-4b93-b02d-031645834282
-- title:
--   Wd6: vlet units
-- statement:
--   The Wd6 construction uses the vlet units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L397-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L397-L403

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

theorem Formalism.FourierDecayAlt.P.Wd6.vlet_units (σ : Site A) (l : Letter K S) (w : List (Letter K S))
    (h : l.intersection_update_fsHerm_neg_one ∉ w.map Letter.intersection_update_fsHerm_neg_one) : ∀ l' ∈ w, ∀ i j, Commute (vlet σ l) (eU l'.intersection_update_fsHerm_neg_one i j) := by sorry
