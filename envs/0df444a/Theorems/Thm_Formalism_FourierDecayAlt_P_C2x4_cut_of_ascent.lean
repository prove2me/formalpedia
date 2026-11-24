-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_cut_of_ascent
-- name    : Formalism.FourierDecayAlt.P.C2x4.cut_of_ascent
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:18.593293+00:00
-- url     : https://prove2.me/theorems/53343410-60d6-4bb6-a330-391cd762e4dd
-- title:
--   C2x4: cut of ascent
-- statement:
--   The C2x4 construction uses the cut of ascent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L19-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L19-L50

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

theorem Formalism.FourierDecayAlt.P.C2x4.cut_of_ascent (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m)
    (ha : a.val + 1 < m) (hasc : w a < w ⟨a.val + 1, ha⟩) : IsCut w a := by sorry
