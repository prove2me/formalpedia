-- Prove2me | Theorems.Thm_Formalism_L2_Pj_DatLin_trace_restrict_complex
-- name    : Formalism.L2.Pj.DatLin.trace_restrict_complex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:40:28.857375+00:00
-- url     : https://prove2.me/theorems/18474b36-1bbb-4b21-985f-b021d91ecd38
-- title:
--   Dat Lin: trace restrict complex
-- statement:
--   The Dat Lin construction uses the trace restrict complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L135-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/DatMat.lean#L135-L144

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_DatMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.DatLin
open Matrix Complex
variable {ι n : Type} [Fintype ι] [Fintype n]

theorem Formalism.L2.Pj.DatLin.trace_restrict_complex {M : Type} [AddCommGroup M] [Module ℂ M] [Module ℝ M]
    [IsScalarTower ℝ ℂ M] [Module.Free ℂ M] [Module.Finite ℂ M] (f : M →ₗ[ℂ] M) :
    LinearMap.trace ℝ M (f.restrictScalars ℝ) = 2 * (LinearMap.trace ℂ M f).re := by sorry
