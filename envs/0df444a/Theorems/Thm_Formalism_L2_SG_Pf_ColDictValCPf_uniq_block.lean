-- Prove2me | Theorems.Thm_Formalism_L2_SG_Pf_ColDictValCPf_uniq_block
-- name    : Formalism.L2.SG.Pf.ColDictValCPf.uniq_block
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:38:17.481849+00:00
-- url     : https://prove2.me/theorems/ecbd2bd2-ab3e-5f8e-8aba-a15551a92106
-- title:
--   Col Dict Val CPf: uniq block
-- statement:
--   The Col Dict Val CPf construction uses the uniq block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighestWeightVectorUnique.lean#L117-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/HighestWeightVectorUnique.lean#L117-L137

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

theorem Formalism.L2.SG.Pf.ColDictValCPf.uniq_block (lam : ι → DomWeight n) (Q : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (hQ : Q ∈ CSpanV lam)
    (hk : ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0) (τ₀ : ι)
    (x : ι × Fin n × Fin n → ℂ) :
    eval x Q = eval (fun p => x (τ₀, p)) (extremal ℂ n (lam τ₀)) *
      eval (fun v => if v.1 = τ₀ then idPoint ℂ n n v.2 else x v) Q := by sorry
