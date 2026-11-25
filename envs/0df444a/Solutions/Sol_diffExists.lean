-- Prove2me | solution 1 for diffExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:00:59.220545+00:00
-- url     : https://prove2.me/submissions/e0a52e04-dad7-4e05-8fdd-734e6acbd6e7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiffGenLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalDifferentGenerators_DiffExistsMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DiffGenLoc
import Theorems.Thm_PI_DiffGenLoc_UnitaryGroupMassFormula_diffExists_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution {F : Type} [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) : PI.DiffGenLoc.DiffExists v :=
  PI.DiffGenLoc.UnitaryGroupMassFormula.diffExists_main v
