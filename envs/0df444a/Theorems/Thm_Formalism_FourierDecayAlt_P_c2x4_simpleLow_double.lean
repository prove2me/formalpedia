-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_c2x4_simpleLow_double
-- name    : Formalism.FourierDecayAlt.P.c2x4_simpleLow_double
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:38:11.521805+00:00
-- url     : https://prove2.me/theorems/c1323edc-f776-4890-aa4a-18513c6baebd
-- title:
--   P: c2x4 simple Low double
-- statement:
--   The P construction uses the c2x4 simple Low double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L231-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L231-L242

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

theorem Formalism.FourierDecayAlt.P.c2x4_simpleLow_double {m : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) :
    C2.simpleLow l = ∑ p : Fin m, ∑ q : Fin m, if p.val = q.val + 1 then l p q else 0 := by sorry
