-- Prove2me | Theorems.Thm_Formalism_ELL_LogarithmWeight_norm_sum_mul_le
-- name    : Formalism.ELL.LogarithmWeight.norm_sum_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:04:06.453252+00:00
-- url     : https://prove2.me/theorems/a0e83c2d-72e3-4898-a269-f3945e25a07c
-- title:
--   Logarithm Weight: norm sum mul le
-- statement:
--   The Logarithm Weight construction uses the norm sum mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L17-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/EllipticTorsionProofs/LogWeight.lean#L17-L23

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_UnitCancel
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_LogWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.LogarithmWeight
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.ELL.LogarithmWeight.norm_sum_mul_le {ι : Type*} (s : Finset ι) (f : ι → K) {w B : ℝ} (hw : 0 < w)
    (hB : 0 ≤ B) (h : ∀ i ∈ s, ‖f i‖ * w ≤ B) : ‖∑ i ∈ s, f i‖ * w ≤ B := by sorry
