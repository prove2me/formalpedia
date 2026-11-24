-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_mem_wLat0_of_mem
-- name    : Formalism.L2.SG.Pf.RedBasicsPf.mem_wLat0_of_mem
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:27:52.061209+00:00
-- url     : https://prove2.me/theorems/c9fa6c18-ba9c-4ed5-ad57-21fe623f9e5e
-- title:
--   Red Basics Pf: mem w Lat0 of mem
-- statement:
--   The Red Basics Pf construction uses the mem w Lat0 of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L42-L44

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

theorem Formalism.L2.SG.Pf.RedBasicsPf.mem_wLat0_of_mem {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) {y : Fin I.n → I.E} (hy : y ∈ I.L) :
    ((a : 𝓞 I.E) : I.E) • y ∈ wLat0 I w := by sorry
