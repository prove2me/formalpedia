-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_diff_bound
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.diff_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:09.248426+00:00
-- url     : https://prove2.me/theorems/a752dbb3-6c38-4132-a888-147866654e75
-- title:
--   Lim: diff bound
-- statement:
--   The Lim construction uses the diff bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1918-L1945
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1918-L1945

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdditiveCharacterPsi
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AffineChangeOfVariables
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RemainderNormLeStrictUpper
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralConvergesAbs
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StandardCharacterExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FourierUniquenessMirabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeakApproximationGL
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WhittakerVanishingImpliesZero
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CuspidalIrreducibleSubrep
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionDerivatives
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EtaleIntegralityFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.EtaleIntegralityFacts Matrix Filter Topology MeasureTheory
noncomputable section
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.diff_bound {a b : ℕ} (hcore : CoreProp a b) (m : ℕ) (β D z t : ℂ) (y : UT (m + 2) → ℂ) {c Rz K' : ℝ}
    (Φ : Mat (m + 1 + 1) → V) (hc0 : 0 < c) (hRz : 1 ≤ Rz) (hz0 : z ≠ 0) (hzR : ‖z‖ ≤ Rz) (hDR : ‖D‖ ≤ Rz)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (ht1 : ‖t‖ ≤ 1)
    (hcof : ∀ τ' : ℂ, ‖τ'‖ ≤ ‖t‖ → c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖)
    (hΦ : ∀ τ' : ℂ, ‖τ'‖ ≤ ‖t‖ → DB 1 Φ (MXY m D τ' (fun _ => z, y)) K' 1) :
    ‖ampE β m Φ D t (fun _ => z, y) - ampE β m Φ D 0 (fun _ => z, y)‖ ≤
      K' * ((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) ^ (a + b) *
        (1 + ‖y‖) ^ (4 * (m + 2) * (a + b)) * ‖t‖ := by sorry
