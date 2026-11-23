-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Easy_dual_volume_power_identity
-- name    : Formalism.FourierDecayAlt.P.Easy.dual_volume_power_identity
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:45.356251+00:00
-- url     : https://prove2.me/theorems/1f0aed39-9e6a-4bdf-b78f-57e74dbeae51
-- title:
--   Easy: dual volume power identity
-- statement:
--   The Easy construction uses the dual volume power identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualVolumePowerIdentity.lean#L9-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DualVolumePowerIdentity.lean#L9-L35

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DualVolumePowerIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Real
open Formalism.FourierDecayAlt.P.Easy

theorem Formalism.FourierDecayAlt.P.Easy.dual_volume_power_identity (ι : Type) [Fintype ι] (c : ι → ℝ) (g rd : ℝ) (r i : ℕ) (hg : 0 < g) (hrd : 0 < rd) :
    (∏ v, c v * (2 * π / g) ^ ((2 * i : ℤ) - 3 - 2 * r)) /
        (g * rd ^ ((2 * r : ℤ) + 3 - 2 * i)) ^ (-(Fintype.card ι : ℤ)) =
      (∏ v, c v) * (2 * π / rd) ^ (((2 * i : ℤ) - 3 - 2 * r) * Fintype.card ι) *
        g ^ (((2 * r + 2 : ℤ) - 2 * ((i : ℤ) - 1)) * Fintype.card ι) := by sorry
