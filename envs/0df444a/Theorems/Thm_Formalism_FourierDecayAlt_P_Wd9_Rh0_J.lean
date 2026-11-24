-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_Rh0_J
-- name    : Formalism.FourierDecayAlt.P.Wd9.Rh0_J
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:47:38.232842+00:00
-- url     : https://prove2.me/theorems/36239c26-b106-4755-a778-3c95f7eed909
-- title:
--   Wd9: Rh0 J
-- statement:
--   The Wd9 construction uses the Rh0 J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L100-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DiagScalarCommuteOfEntries.lean#L100-L112

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

theorem Formalism.FourierDecayAlt.P.Wd9.Rh0_J (a : S) (D d : K) (h : d = 1 - D) (hD : D ≠ 0) (hD1 : D ≠ 1) :
    Rh0 a D * d0 (ins a JJ) = (D / (D - 1)) • (d0 (ins a JJ) * Rht0 a d) := by sorry
