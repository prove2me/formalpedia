-- Prove2me | solution 1 for unimodular_genus_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:14.503936+00:00
-- url     : https://prove2.me/submissions/c76fdd4a-df87-4c0b-a9d7-5667465ce545

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnimodGenus
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularGenus_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnimodGenus
import Theorems.Thm_PI_UG_W_isomLocStd
import Theorems.Thm_PI_UG_W_unimodGenus_of
import Theorems.Thm_PI_UG_W_unimodLocal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : PI.UnimodGenus :=
  PI.UG.W.unimodGenus_of PI.UG.W.unimodLocal PI.UG.W.isomLocStd
