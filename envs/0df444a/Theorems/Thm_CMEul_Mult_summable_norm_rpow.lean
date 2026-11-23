-- Prove2me | Theorems.Thm_CMEul_Mult_summable_norm_rpow
-- name    : CMEul.Mult.summable_norm_rpow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:26:59.360159+00:00
-- url     : https://prove2.me/theorems/010e6058-ef37-4ff8-8d72-9319a41caeac
-- title:
--   Mult: summable norm rpow
-- statement:
--   The Mult construction uses the summable norm rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L42-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L42-L74

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

theorem CMEul.Mult.summable_norm_rpow {K : Type} [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) :
    Summable (fun P : {P : Ideal (𝓞 K) // P.IsMaximal} => ((Ideal.absNorm P.1 : ℕ) : ℝ) ^ (-s)) := by sorry
