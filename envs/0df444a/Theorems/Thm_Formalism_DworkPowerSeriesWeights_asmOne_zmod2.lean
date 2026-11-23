-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmOne_zmod2
-- name    : Formalism.DworkPowerSeriesWeights.asmOne_zmod2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:59:31.810404+00:00
-- url     : https://prove2.me/theorems/3a7dd5da-2908-4cee-bdbb-d1f8a2199dba
-- title:
--   Dwork Power Series Weights: asm One zmod2
-- statement:
--   The Dwork Power Series Weights construction uses the asm One zmod2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L82-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/AsmOne.lean#L82-L84

import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmRDotAddRight
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_AsmOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.asmOne_zmod2 : ∀ s s' a b : ZMod 2, s.val % 2 = 0 → s'.val % 2 = 1 → s + a = s' + b →
    a + b = 1 := by sorry
