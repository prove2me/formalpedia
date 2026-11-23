-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_diagScalar_commute_of_entries
-- name    : Formalism.FourierDecayAlt.P.Wd9.diagScalar_commute_of_entries
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:54.841537+00:00
-- url     : https://prove2.me/theorems/c828ffcc-f544-4f47-898f-0ba8e2a61122
-- title:
--   Wd9: diag Scalar commute of entries
-- statement:
--   The Wd9 construction uses the diag Scalar commute of entries property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L80-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L80-L83

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))

theorem Formalism.FourierDecayAlt.P.Wd9.diagScalar_commute_of_entries {b : SlopeTestRemainingChoices S A} {M : M2 (SlopeTestRemainingChoices S A)} (h : ∀ i j, Commute b (M i j)) :
    d0 b * M = M * d0 b := by sorry
