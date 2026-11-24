-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_smooth_zero
-- name    : Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T15:51:21.924304+00:00
-- url     : https://prove2.me/theorems/908415a5-40f7-4291-8693-a6718f89e6e8
-- title:
--   Translation Bessel Vanishing: smooth zero
-- statement:
--   The Translation Bessel Vanishing construction uses the smooth zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNeZeroOfCyclicOrbit.lean#L90-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNeZeroOfCyclicOrbit.lean#L90-L95

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open PI.UpqRep
open Formalism.FourierDecayAlt.P.TranslationBesselVanishing
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_zero {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} :
    (0 : H) ∈ smoothVecs (k := k) (r := r) σ := by sorry
