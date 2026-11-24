-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_p_sum_le
-- name    : Formalism.FourierDecayAlt.P.GeometricRayBounds.p_sum_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T16:16:49.814712+00:00
-- url     : https://prove2.me/theorems/2c9828e9-0490-453b-ae24-a6e2a251aa1d
-- title:
--   Geometric Ray Bounds: p sum le
-- statement:
--   The Geometric Ray Bounds construction uses the p sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragingVanishes.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragingVanishes.lean#L29-L35

import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragingVanishes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GeometricRayBounds

theorem Formalism.FourierDecayAlt.P.GeometricRayBounds.p_sum_le {V : Type*} [AddCommGroup V] [Module ℂ V] (p : Seminorm ℂ V) {ι : Type*} (S : Finset ι)
    (f : ι → V) : p (∑ i ∈ S, f i) ≤ ∑ i ∈ S, p (f i) := by sorry
