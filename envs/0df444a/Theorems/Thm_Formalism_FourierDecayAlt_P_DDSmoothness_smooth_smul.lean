-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_smul
-- name    : Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:51:33.745368+00:00
-- url     : https://prove2.me/theorems/a91b9c3f-9949-45f6-94b1-1fe650d606b4
-- title:
--   DDSmoothness: smooth smul
-- statement:
--   The DDSmoothness construction uses the smooth smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothAdd.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SmoothAdd.lean#L37-L43

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_Smooth
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate ContDiff
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul {σ : Mx k r → (H →L[ℂ] H)} (a : ℂ) {v : H} (hv : v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ) :
    a • v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := by sorry
