-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_cut_preserves
-- name    : Formalism.FourierDecayAlt.P.C2x4.cut_preserves
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:11:20.984799+00:00
-- url     : https://prove2.me/theorems/b3246d32-54be-424b-b23e-d5282425e013
-- title:
--   C2x4: cut preserves
-- statement:
--   The C2x4 construction uses the cut preserves property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L52-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RelevantMonotoneOfParts.lean#L52-L76

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

theorem Formalism.FourierDecayAlt.P.C2x4.cut_preserves (w : Equiv.Perm (Fin m)) (c : Fin m) (hc : IsCut w c) (x : Fin m) :
    x ≤ c ↔ w x ≤ c := by sorry
