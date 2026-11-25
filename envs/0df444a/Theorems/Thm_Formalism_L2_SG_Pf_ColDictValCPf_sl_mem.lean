-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_sl_mem
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.sl_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:28:49.267774+00:00
-- url     : https://prove2.me/theorems/0f2dda21-8834-439a-8bb3-445cca14a549
-- title:
--   Col Dict Val CPf: sl mem
-- statement:
--   The Col Dict Val CPf construction uses the sl mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighestWeightVectorUnique.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighestWeightVectorUnique.lean#L79-L90

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_HWLine
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_WeylLeDual
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_SumIcoTsubTelescope
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_RowDivStable
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LHwrowLemmas
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_HighestWeightVectorUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf MvPolynomial
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

theorem Formalism.L2.SG.Pf.ColDictValCPf.sl_mem (lam : ι → DomWeight n) (τ₀ : ι) (x : ι × Fin n × Fin n → ℂ)
    {Q : MvPolynomial (ι × Fin n × Fin n) ℂ} (hQ : Q ∈ CSpanV lam) :
    sl τ₀ x Q ∈ delSq ℂ n (lam τ₀) := by sorry
