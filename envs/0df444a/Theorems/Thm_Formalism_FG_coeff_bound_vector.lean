-- Prove2me | Theorems.Thm_Formalism_FG_coeff_bound_vector
-- name    : Formalism.FG.coeff_bound_vector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:23.466357+00:00
-- url     : https://prove2.me/theorems/e1c48446-2598-4d1e-a2e0-17380fcf5bd9
-- title:
--   FG: coeff bound vector
-- statement:
--   The FG construction uses the coeff bound vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffV.lean#L144-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffV.lean#L144-L144

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w

theorem Formalism.FG.coeff_bound_vector : Formalism.FG.CoeffBoundV.{u, v, w} := by sorry
