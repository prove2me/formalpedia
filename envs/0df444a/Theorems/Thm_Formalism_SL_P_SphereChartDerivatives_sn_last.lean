-- Prove2me | Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- name    : Formalism.SL.P.SphereChartDerivatives.sn_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:15.971029+00:00
-- url     : https://prove2.me/theorems/904ebb84-1c5f-477e-94ab-cfa7ffd5b52c
-- title:
--   Sphere Chart Derivatives: sn last
-- statement:
--   The Sphere Chart Derivatives construction uses the sn last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/HasDerivAtSphereChartLast.lean#L16-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/HasDerivAtSphereChartLast.lean#L16-L16

import Mathlib
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementSB
import Definitions.Def_Formalism_SobolevGaussianKernels_StatementLF
import Definitions.Def_Formalism_SobolevGaussianKernels_GaussianKernelBounds_HasDerivAtSphereChartLast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.SL Formalism.SL.P
open MeasureTheory Formalism.SL.SB
open scoped ContDiff
open Formalism.SL.P.SphereChartDerivatives
variable {n : ℕ}

theorem Formalism.SL.P.SphereChartDerivatives.sn_last (t : ℝ) (y : Fin n → ℝ) : sn t y (Fin.last n) = t := by sorry
