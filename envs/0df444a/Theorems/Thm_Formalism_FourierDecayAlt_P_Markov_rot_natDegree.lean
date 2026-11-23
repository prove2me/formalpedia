-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Markov_rot_natDegree
-- name    : Formalism.FourierDecayAlt.P.Markov.rot_natDegree
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:33.51582+00:00
-- url     : https://prove2.me/theorems/2cf856e9-8c77-4a29-9881-73083c8fa774
-- title:
--   Markov: rot nat Degree
-- statement:
--   The Markov construction uses the rot nat Degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L158-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/Markov.lean#L158-L181

import Definitions.Def_Formalism_HermitianCurvature_StatementE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Markov
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Markov
open Polynomial Real Finset

theorem Formalism.FourierDecayAlt.P.Markov.rot_natDegree (a b : ℝ) (m : ℕ) :
    (rot a b m).1.natDegree ≤ m ∧ (rot a b (m + 1)).2.natDegree ≤ m ∧
      ((1 - X ^ 2) * (rot a b m).2).natDegree ≤ m + 1 := by sorry
