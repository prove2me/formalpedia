-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_diagScalar
-- name    : Formalism.FourierDecayAlt.P.Wd9.freeOf_diagScalar
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:01.418542+00:00
-- url     : https://prove2.me/theorems/7d057a2a-680f-4df6-9396-070fa9b7fb0d
-- title:
--   Wd9: free Of diag Scalar
-- statement:
--   The Wd9 construction uses the free Of diag Scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L45-L50

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

theorem Formalism.FourierDecayAlt.P.Wd9.freeOf_diagScalar {a : S} {b : SlopeTestRemainingChoices S A} (h : FreeOf a b) : FreeOf2 a (d0 b) := by sorry
