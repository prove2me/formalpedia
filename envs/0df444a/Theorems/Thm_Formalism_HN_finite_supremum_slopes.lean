-- Prove2me | Theorems.Thm_Formalism_HN_finite_supremum_slopes
-- name    : Formalism.HN.finite_supremum_slopes
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:10.8498+00:00
-- url     : https://prove2.me/theorems/d59ef862-2edf-4c53-8e97-a0f5995e0479
-- title:
--   HN: finite supremum slopes
-- statement:
--   The HN construction uses the finite supremum slopes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/FinSup.lean#L14-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/FinSup.lean#L14-L64

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_FinSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN

theorem Formalism.HN.finite_supremum_slopes : FinSup := by sorry
