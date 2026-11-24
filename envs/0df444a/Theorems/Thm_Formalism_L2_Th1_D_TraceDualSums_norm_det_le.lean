-- Prove2me | Theorems.Thm_Formalism_L2_Th1_D_TraceDualSums_norm_det_le
-- name    : Formalism.L2.Th1.D.TraceDualSums.norm_det_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:47:29.110965+00:00
-- url     : https://prove2.me/theorems/a5afd24d-9ac5-4b9c-8b08-f7c9f0811929
-- title:
--   Trace Dual Sums: norm det le
-- statement:
--   The Trace Dual Sums construction uses the norm det le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TraceDualExists.lean#L33-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/KummerThetaLogarithms/TraceDualExists.lean#L33-L41

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.D.TraceDualSums

theorem Formalism.L2.Th1.D.TraceDualSums.norm_det_le {K : Type} [NormedField K] [IsUltrametricDist K] {n : Type} [Fintype n]
    [DecidableEq n] (M : Matrix n n K) (h : ∀ i j, ‖M i j‖ ≤ 1) : ‖M.det‖ ≤ 1 := by sorry
