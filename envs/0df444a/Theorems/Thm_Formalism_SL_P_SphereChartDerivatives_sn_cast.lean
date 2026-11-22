-- Prove2me | Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
-- name    : Formalism.SL.P.SphereChartDerivatives.sn_cast
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:48:28.60736+00:00
-- url     : https://prove2.me/theorems/e8470db7-89a3-4c75-b0a4-b7a1781745c7
-- title:
--   Sphere Chart Derivatives: sn cast
-- statement:
--   The Sphere Chart Derivatives construction uses the sn cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/HasDerivAtSphereChartLast.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/HasDerivAtSphereChartLast.lean#L17-L18

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

theorem Formalism.SL.P.SphereChartDerivatives.sn_cast (t : ℝ) (y : Fin n → ℝ) (k : Fin n) : sn t y (Fin.castSucc k) = y k := by sorry
