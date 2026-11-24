-- Prove2me | solution 1 for qnEabPres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:40.175309+00:00
-- url     : https://prove2.me/submissions/768dcb15-222c-42e4-8f75-71ada0d7104a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DerivativePreservation_EabPresMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabPres
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_left
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_lin
import Theorems.Thm_Formalism_FourierDecayAlt_Q_EabLie_eab_smooth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem _root_.solution : Formalism.FourierDecayAlt.Q.EabPres := by
  intro E _ _ k r z i D a b f f₂ s hD hf hf₂
  refine ⟨Formalism.FourierDecayAlt.Q.EabLie.eab_smooth i D a b f hf, fun _ hL => ?_, fun g hg => ?_⟩
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_left i z D hD a b f hf hL
  · exact Formalism.FourierDecayAlt.Q.EabLie.eab_lin i D a b f f₂ s hf hf₂ g hg
