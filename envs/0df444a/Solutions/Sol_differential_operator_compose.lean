-- Prove2me | solution 1 for differential_operator_compose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:03:20.61702+00:00
-- url     : https://prove2.me/submissions/b9ca781a-c6ef-4449-adbf-013aa038cc6e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UsCompose
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_composeDD_of
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_degD
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_degDP
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_expand


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.U.ComposeDD :=
  PI.UnitaryGroupMassFormula.UsCompose.composeDD_of (fun _ X q => PI.UnitaryGroupMassFormula.UsCompose.degDP X q)
    (fun k j ρ => PI.UnitaryGroupMassFormula.UsCompose.degD k j ρ) PI.UnitaryGroupMassFormula.UsCompose.expand
