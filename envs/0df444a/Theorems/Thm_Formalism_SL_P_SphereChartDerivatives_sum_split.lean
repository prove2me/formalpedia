-- Prove2me | Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sum_split
-- name    : Formalism.SL.P.SphereChartDerivatives.sum_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:50.911098+00:00
-- url     : https://prove2.me/theorems/7d5ae1d0-88e8-4dac-9ef2-a793edb7e50c
-- title:
--   Sphere Chart Derivatives: sum split
-- statement:
--   The Sphere Chart Derivatives construction uses the sum split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/HasDerivAtSphereChartLast.lean#L24-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SobolevGaussianKernels/GaussianKernelBounds/HasDerivAtSphereChartLast.lean#L24-L61

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

theorem Formalism.SL.P.SphereChartDerivatives.sum_split (f : Finset (Fin (n + 1)) → ℝ) :
    ∑ α : Finset (Fin (n + 1)), f α =
      ∑ β : Finset (Fin n), f (β.map Fin.castSuccEmb) +
        ∑ β : Finset (Fin n), f (insert (Fin.last n) (β.map Fin.castSuccEmb)) := by sorry
