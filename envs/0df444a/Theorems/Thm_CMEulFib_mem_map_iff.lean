-- Prove2me | Theorems.Thm_CMEulFib_mem_map_iff
-- name    : CMEulFib.mem_map_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T00:19:17.511108+00:00
-- url     : https://prove2.me/theorems/9763446b-63f9-4abd-b65c-e78fdc7e8dd7
-- title:
--   CMEul Fib: mem map iff
-- statement:
--   The CMEul Fib construction uses the mem map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/FibreShapeOf.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMEulerProducts/FibreShapeOf.lean#L17-L19

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_StepRegroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMDegreeEquality_FinrankEqTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMEulerProducts_FibreShapeOf
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
open CMEulFib
open Formalism.L2.SG.MassRatio Formalism.HermitianLatticesTheory

theorem CMEulFib.mem_map_iff {B : Type*} [CommRing B] (σ : B ≃+* B) (hinv : ∀ x, σ (σ x) = x)
    (P : Ideal B) (y : B) : y ∈ P.map σ ↔ σ y ∈ P := by sorry
