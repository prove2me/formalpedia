-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GeometricRayBounds_exists_dir
-- name    : Formalism.FourierDecayAlt.P.GeometricRayBounds.exists_dir
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:15:17.860187+00:00
-- url     : https://prove2.me/theorems/81154c8a-10aa-4f80-ac26-edd6c4bc6b25
-- title:
--   Geometric Ray Bounds: exists dir
-- statement:
--   The Geometric Ray Bounds construction uses the exists dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragingVanishes.lean#L9-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AveragingVanishes.lean#L9-L27

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

theorem Formalism.FourierDecayAlt.P.GeometricRayBounds.exists_dir {ι : Type*} (S : Finset ι) (c : ι → ℂ) (hc : ∀ i ∈ S, c i ≠ 0) :
    ∃ u : ℂ, u ≠ 0 ∧ ∀ i ∈ S, (c i * u).re ≠ 0 := by sorry
