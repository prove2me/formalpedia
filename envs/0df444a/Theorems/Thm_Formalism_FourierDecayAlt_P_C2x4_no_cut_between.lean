-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_no_cut_between
-- name    : Formalism.FourierDecayAlt.P.C2x4.no_cut_between
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:30:11.689055+00:00
-- url     : https://prove2.me/theorems/85c65be7-487c-4bd6-ae79-b76422590a24
-- title:
--   C2x4: no cut between
-- statement:
--   The C2x4 construction uses the no cut between property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L108-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L108-L125

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}

theorem Formalism.FourierDecayAlt.P.C2x4.no_cut_between (w : Equiv.Perm (Fin m)) (a b j : Fin m) (hab : blk w a = blk w b)
    (hj1 : a ≤ j) (hj2 : j < b) : ¬ IsCut w j := by sorry
