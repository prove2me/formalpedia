-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_lamAf_w_le
-- name    : Formalism.L2.SG.Pf.RedBasicsPf.lamAf_w_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:09.903638+00:00
-- url     : https://prove2.me/theorems/f3a62e8a-f948-46f0-8d23-c24dd254b09c
-- title:
--   Red Basics Pf: lam Af w le
-- statement:
--   The Red Basics Pf construction uses the lam Af w le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L223-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RedBasicsPf.lean#L223-L239

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

theorem Formalism.L2.SG.Pf.RedBasicsPf.lamAf_w_le (S : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F))
    (h : ∀ a ∈ w.asIdeal, ∀ y ∈ I.L, iv I (((a : 𝓞 I.E) : I.E) • y) ∈ S) :
    lamAf (F := I.F) (wLat0 I w) ≤ S := by sorry
