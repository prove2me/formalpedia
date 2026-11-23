-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd8_word_product_formula_general
-- name    : Formalism.FourierDecayAlt.P.Wd8.word_product_formula_general
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:18.238956+00:00
-- url     : https://prove2.me/theorems/21333c29-2ce8-4945-bb34-1b0a66bfcdfc
-- title:
--   Wd8: word product formula general
-- statement:
--   The Wd8 construction uses the word product formula general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L541-L597
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LiftMatrixTransferConjTransposeCommute.lean#L541-L597

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LiftMatrixTransferConjTransposeCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd8
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd8.word_product_formula_general (sites : List (Site A)) (w : List (Letter K S))
    (hs : sites.Pairwise SitesCommute) (hw : (w.map Letter.intersection_update_fsHerm_neg_one).Nodup) (z : Ix S) :
    uw sites w z =
      if ∀ c, c ∉ w.map Letter.intersection_update_fsHerm_neg_one → z c = 0 then
        (w.map fun l => (sites.map (lm l)).prod (z l.intersection_update_fsHerm_neg_one) 0).prod
      else 0 := by sorry
