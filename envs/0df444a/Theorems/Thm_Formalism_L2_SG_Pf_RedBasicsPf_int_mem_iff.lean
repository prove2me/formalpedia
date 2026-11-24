-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_int_mem_iff
-- name    : Formalism.L2.SG.Pf.RedBasicsPf.int_mem_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:52.177032+00:00
-- url     : https://prove2.me/theorems/f72ba873-5aa8-41c5-8c21-fbe766bc38fd
-- title:
--   Red Basics Pf: int mem iff
-- statement:
--   The Red Basics Pf construction uses the int mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L79-L82

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

theorem Formalism.L2.SG.Pf.RedBasicsPf.int_mem_iff {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (c : ℤ) :
    (c : 𝓞 I.E) ∈ w.asIdeal ↔ (p : ℤ) ∣ c := by sorry
