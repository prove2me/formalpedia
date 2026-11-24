-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_exists_ideal_element_not_mem
-- name    : Formalism.L2.SG.Pf.RedBasicsPf.exists_ideal_element_not_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:27:00.576937+00:00
-- url     : https://prove2.me/theorems/475b22d7-f7c5-4838-8fdd-68a755a55856
-- title:
--   Red Basics Pf: exists ideal element not mem
-- statement:
--   The Red Basics Pf construction uses the exists ideal element not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L286-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L286-L308

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))

theorem Formalism.L2.SG.Pf.RedBasicsPf.exists_ideal_element_not_mem : ∃ t β : 𝓞 I.E, t ∈ w.asIdeal ∧ t ≠ 0 ∧ (∀ a ∈ w.asIdeal, ∃ g, β * a = t * g) ∧
    β ∉ w.asIdeal := by sorry
