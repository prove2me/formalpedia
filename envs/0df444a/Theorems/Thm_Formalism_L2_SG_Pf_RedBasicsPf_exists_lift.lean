-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_exists_lift
-- name    : Formalism.L2.SG.Pf.RedBasicsPf.exists_lift
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:22.28738+00:00
-- url     : https://prove2.me/theorems/53aa3768-a50a-403b-b004-757b8927f162
-- title:
--   Red Basics Pf: exists lift
-- statement:
--   The Red Basics Pf construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L97-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L97-L106

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_lift

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

theorem Formalism.L2.SG.Pf.RedBasicsPf.exists_lift (y : I.L) {d : ℕ} (e : Module.Basis (Fin d) (𝓞 I.E ⧸ w.asIdeal) (RedQ I w))
    (b' : Fin d → I.L) (hb' : ∀ i, Submodule.Quotient.mk (b' i) = e i) :
    ∃ α : Fin d → 𝓞 I.E, y - ∑ i, α i • b' i ∈ (w.asIdeal • (⊤ : Submodule (𝓞 I.E) I.L)) := by sorry
