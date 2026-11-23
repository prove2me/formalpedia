-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_Rht0_J
-- name    : Formalism.FourierDecayAlt.P.Wd9.Rht0_J
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:42.466653+00:00
-- url     : https://prove2.me/theorems/587ffe3e-089d-4712-b1cc-e63a205fc290
-- title:
--   Wd9: Rht0 J
-- statement:
--   The Wd9 construction uses the Rht0 J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L114-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L114-L126

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

theorem Formalism.FourierDecayAlt.P.Wd9.Rht0_J (a : S) (d D : K) (h : D = 1 - d) (hd : d ≠ 0) (hd1 : d ≠ 1) :
    Rht0 a d * d0 (ins a JJ) = (d / (d - 1)) • (d0 (ins a JJ) * Rh0 a D) := by sorry
