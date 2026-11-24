-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_smooth_smul
-- name    : Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:31:17.255677+00:00
-- url     : https://prove2.me/theorems/0272da44-5e7b-40f6-bbc4-0a210b69cb85
-- title:
--   Translation Bessel Vanishing: smooth smul
-- statement:
--   The Translation Bessel Vanishing construction uses the smooth smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNeZeroOfCyclicOrbit.lean#L81-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNeZeroOfCyclicOrbit.lean#L81-L88

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

theorem Formalism.FourierDecayAlt.P.TranslationBesselVanishing.smooth_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)} (c : ℂ) {x : H}
    (hx : x ∈ smoothVecs (k := k) (r := r) σ) : c • x ∈ smoothVecs (k := k) (r := r) σ := by sorry
