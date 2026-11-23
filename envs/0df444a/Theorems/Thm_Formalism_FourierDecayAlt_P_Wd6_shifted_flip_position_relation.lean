-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_shifted_flip_position_relation
-- name    : Formalism.FourierDecayAlt.P.Wd6.shifted_flip_position_relation
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:46:03.234814+00:00
-- url     : https://prove2.me/theorems/f048f6fc-1e58-4670-9fcb-59f94d5d380c
-- title:
--   Wd6: shifted flip position relation
-- statement:
--   The Wd6 construction uses the shifted flip position relation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L210-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L210-L242

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
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem Formalism.FourierDecayAlt.P.Wd6.shifted_flip_position_relation (a : S) (M N : M2 A) (D : K) (h : Rel M N D) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * lift0 M * d0 (ins a (lift0 N)) =
      d0 (ins a (lift0 N)) * lift0 M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by sorry
