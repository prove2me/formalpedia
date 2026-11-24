-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_TranslationBesselVanishing_uh_mul
-- name    : Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:30:09.994852+00:00
-- url     : https://prove2.me/theorems/bc504ade-e857-4aea-b63c-d3762bc4059b
-- title:
--   Translation Bessel Vanishing: uh mul
-- statement:
--   The Translation Bessel Vanishing construction uses the uh mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNeZeroOfCyclicOrbit.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BesselNeZeroOfCyclicOrbit.lean#L19-L25

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

theorem Formalism.FourierDecayAlt.P.TranslationBesselVanishing.uh_mul {g h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : hᴴ * Hpk k r * h = Hpk k r) (hg : gᴴ * Hpk k r * g = Hpk k r) :
    (h * g)ᴴ * Hpk k r * (h * g) = Hpk k r := by sorry
