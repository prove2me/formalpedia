-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_ins_mul_io
-- name    : Formalism.FourierDecayAlt.P.Wd6.ins_mul_io
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:38.135077+00:00
-- url     : https://prove2.me/theorems/8ee35fcd-d348-4ee3-8b65-653b28a44835
-- title:
--   Wd6: ins mul io
-- statement:
--   The Wd6 construction uses the ins mul io property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EntryCommuteTransposedRMatrix.lean#L192-L195

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

theorem Formalism.FourierDecayAlt.P.Wd6.ins_mul_io (a : S) (x : A) (N : M2 A) :
    ins a (lift0 N) * (io x : SlopeTestRemainingChoices S A) = ∑ r, ∑ s, eU a r s * io (N r s * x) := by sorry
