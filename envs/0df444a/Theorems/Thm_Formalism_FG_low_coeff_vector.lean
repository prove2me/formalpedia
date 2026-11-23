-- Prove2me | Theorems.Thm_Formalism_FG_low_coeff_vector
-- name    : Formalism.FG.low_coeff_vector
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:00.115659+00:00
-- url     : https://prove2.me/theorems/fe422fd6-7324-471f-9e12-1e06013b0443
-- title:
--   FG: low coeff vector
-- statement:
--   The FG construction uses the low coeff vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffExpandEqZero.lean#L43-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffExpandEqZero.lean#L43-L55

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffExpandEqZero
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
open Formalism Formalism.FG
open Formalism.G

theorem Formalism.FG.low_coeff_vector : Formalism.FG.LowCoeffV.{u, v, w} := by sorry
