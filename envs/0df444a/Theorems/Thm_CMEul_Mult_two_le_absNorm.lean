-- Prove2me | Theorems.Thm_CMEul_Mult_two_le_absNorm
-- name    : CMEul.Mult.two_le_absNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:39:17.967435+00:00
-- url     : https://prove2.me/theorems/762c38e4-6380-4ef2-a20b-f02292d2d9fc
-- title:
--   Mult: two le abs Norm
-- statement:
--   The Mult construction uses the two le abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/EulerFactorsMultipliable.lean#L12-L20

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

theorem CMEul.Mult.two_le_absNorm {K : Type} [Field K] [NumberField K] (P : Ideal (𝓞 K)) (hP : P.IsMaximal) :
    2 ≤ Ideal.absNorm P := by sorry
