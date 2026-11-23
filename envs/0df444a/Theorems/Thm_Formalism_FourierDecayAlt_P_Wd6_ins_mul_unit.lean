-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_mul_unit
-- name    : Formalism.FourierDecayAlt.P.Wd6.ins_mul_unit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:45.862808+00:00
-- url     : https://prove2.me/theorems/516bfafd-d721-4b8c-aa04-553b0e7f2889
-- title:
--   Wd6: ins mul unit
-- statement:
--   The Wd6 construction uses the ins mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L203-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L203-L208

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

theorem Formalism.FourierDecayAlt.P.Wd6.ins_mul_unit (a : S) (k j : Fin 2) (x : A) (N : M2 A) :
    ins a (lift0 N) * (io x * (eU a k j : SlopeTestRemainingChoices S A)) = ∑ r, eU a r j * io (N r k * x) := by sorry
