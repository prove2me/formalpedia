-- Prove2me | Theorems.Thm_CMEul_Mult_card_le
-- name    : CMEul.Mult.card_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:37.005319+00:00
-- url     : https://prove2.me/theorems/406a2848-e6de-4804-a648-93389b68d64c
-- title:
--   Mult: card le
-- statement:
--   The Mult construction uses the card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L22-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L22-L40

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_EulerFactorsMultipliable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open CMEul CMEul.Mult
open Formalism.HermitianLatticesTheory

theorem CMEul.Mult.card_le {K : Type} [Field K] [NumberField K] (n : ℕ) (hn : 2 ≤ n)
    (s : Finset {P : Ideal (𝓞 K) // P.IsMaximal}) (hs : ∀ P ∈ s, Ideal.absNorm P.1 = n) :
    s.card ≤ Module.finrank ℤ (𝓞 K) := by sorry
