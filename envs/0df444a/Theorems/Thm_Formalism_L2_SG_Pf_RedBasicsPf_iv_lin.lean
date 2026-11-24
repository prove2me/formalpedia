-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_iv_lin
-- name    : Formalism.L2.SG.Pf.RedBasicsPf.iv_lin
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:08.364+00:00
-- url     : https://prove2.me/theorems/44e59ad1-14c6-45d4-ba43-0bcca2a5f89f
-- title:
--   Red Basics Pf: iv lin
-- statement:
--   The Red Basics Pf construction uses the iv lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L351-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L351-L355

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

theorem Formalism.L2.SG.Pf.RedBasicsPf.iv_lin (l : Fin I.n → I.E) {m : ℕ} (b : Fin m → Fin I.n → I.E) (c : Fin m → ℤ) :
    iv I (l - ∑ i, (c i : I.E) • b i) = iv I l - ∑ i, (c i : I.E ⊗[I.F] Af I.F) • iv I (b i) := by sorry
