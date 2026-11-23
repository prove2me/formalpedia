-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Sz4_vand_words_ratio
-- name    : Formalism.FourierDecayAlt.P.Sz4.vand_words_ratio
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:03.171148+00:00
-- url     : https://prove2.me/theorems/544f1507-1c50-480c-b847-a8b61a8135d5
-- title:
--   Sz4: vand words ratio
-- statement:
--   The Sz4 construction uses the vand words ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L358-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumInvSqLeSub.lean#L358-L368

import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumInvSqLeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Sz4
open Finset Formalism.FourierDecayAlt.Sz

theorem Formalism.FourierDecayAlt.P.Sz4.vand_words_ratio (c : Cfg) (de : ℕ → ℝ) (hw : IsWord c.k de) (p : ℕ) (hp : p + 1 ≤ c.k)
    (h : p + 2 ≤ c.k ∨ c.top = false) :
    Vand p (fun i => c.u de (i + 1)) = Rde p de * Vand p c.v := by sorry
