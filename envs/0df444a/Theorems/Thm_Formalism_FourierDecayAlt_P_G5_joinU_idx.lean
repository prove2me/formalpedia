-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_G5_joinU_idx
-- name    : Formalism.FourierDecayAlt.P.G5.joinU_idx
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:08.195632+00:00
-- url     : https://prove2.me/theorems/9cf9ba59-d8e2-4f31-976c-bb4c61a01f47
-- title:
--   G5: join U idx
-- statement:
--   The G5 construction uses the join U idx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L240-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousInvUpper.lean#L240-L242

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousInvUpper
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
set_option linter.unusedSimpArgs false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G5
open Formalism.FourierDecayAlt.G

theorem Formalism.FourierDecayAlt.P.G5.joinU_idx {n : ℕ} (q : (UT n → ℂ) × (Fin n → ℂ)) (s : UT n ⊕ Fin n) :
    joinU q (idxEquiv n s) = Sum.elim q.1 q.2 s := by sorry
