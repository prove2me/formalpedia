-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_io_mul_ins
-- name    : Formalism.FourierDecayAlt.P.Wd6.io_mul_ins
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:55.904605+00:00
-- url     : https://prove2.me/theorems/4fcfe601-49ae-4830-9871-a3a1b46b5cd0
-- title:
--   Wd6: io mul ins
-- statement:
--   The Wd6 construction uses the io mul ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L185-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L185-L190

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

theorem Formalism.FourierDecayAlt.P.Wd6.io_mul_ins (a : S) (x : A) (N : M2 A) :
    (io x : SlopeTestRemainingChoices S A) * ins a (lift0 N) = ∑ r, ∑ s, eU a r s * io (x * N r s) := by sorry
