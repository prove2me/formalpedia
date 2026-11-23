-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_EtaleIntegralityFacts_Lim_diff_key
-- name    : Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.diff_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:37.132748+00:00
-- url     : https://prove2.me/theorems/f8e857c1-dab2-4986-bdd3-502294305b32
-- title:
--   Lim: diff key
-- statement:
--   The Lim construction uses the diff key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1849-L1916
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/EtaleIntegralityFacts.lean#L1849-L1916

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

theorem Formalism.FourierDecayAlt.P.EtaleIntegralityFacts.Lim.diff_key {a b : ℕ} (hcore : CoreProp a b) (m : ℕ) (β D z τ' : ℂ) (y : UT (m + 2) → ℂ) {c Rz K' : ℝ}
    (Φ : Mat (m + 1 + 1) → V) (hc0 : 0 < c) (hRz : 1 ≤ Rz) (hz0 : z ≠ 0) (hzR : ‖z‖ ≤ Rz) (hDR : ‖D‖ ≤ Rz)
    (hcz : c ≤ ‖z‖ ^ (m + 1)) (hτ1 : ‖τ'‖ ≤ 1) (hl : c / 2 ≤ ‖cofXY m τ' (fun _ => z, y)‖)
    (hΦ : DB 1 Φ (MXY m D τ' (fun _ => z, y)) K' 1) :
    DB 1 (fun v : ℂ => ampE β m Φ D v (fun _ => z, y)) τ'
      (K' * (((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) * (1 + ‖y‖) ^ (4 * (m + 2))) ^ a)
      ((((4 * ((m : ℝ) + 2) ^ 2 + Rz + ‖β‖) ^ (4 * (m + 2)) + 2 / c) * (1 + ‖y‖) ^ (4 * (m + 2))) ^ b) := by sorry
