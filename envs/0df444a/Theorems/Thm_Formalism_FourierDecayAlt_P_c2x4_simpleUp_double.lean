-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x4_simpleUp_double
-- name    : Formalism.FourierDecayAlt.P.c2x4_simpleUp_double
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:38:12.883202+00:00
-- url     : https://prove2.me/theorems/33042415-8a82-403f-84e4-aa181a2dee74
-- title:
--   P: c2x4 simple Up double
-- statement:
--   The P construction uses the c2x4 simple Up double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L244-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L244-L254

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
open C2x4

theorem Formalism.FourierDecayAlt.P.c2x4_simpleUp_double {m : ℕ} (u : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleUp u = ∑ a : Fin m, ∑ b : Fin m, if b.val = a.val + 1 then u a b else 0 := by sorry
