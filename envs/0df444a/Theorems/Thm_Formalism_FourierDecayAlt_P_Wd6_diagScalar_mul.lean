-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_diagScalar_mul
-- name    : Formalism.FourierDecayAlt.P.Wd6.diagScalar_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:48:07.708797+00:00
-- url     : https://prove2.me/theorems/7c27f439-6a54-4790-a860-5784b5332227
-- title:
--   Wd6: diag Scalar mul
-- statement:
--   The Wd6 construction uses the diag Scalar mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L147-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L147-L149

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

theorem Formalism.FourierDecayAlt.P.Wd6.diagScalar_mul (x y : SlopeTestRemainingChoices S A) : d0 (x * y) = d0 x * d0 y := by sorry
