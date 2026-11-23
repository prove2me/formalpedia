-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MeanBoundsLimits_bdd_inner
-- name    : Formalism.FourierDecayAlt.P.MeanBoundsLimits.bdd_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:31.602574+00:00
-- url     : https://prove2.me/theorems/e241b7b6-da1f-46bf-9b9d-139213469aa1
-- title:
--   Mean Bounds Limits: bdd inner
-- statement:
--   The Mean Bounds Limits construction uses the bdd inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanBoundsLimits.lean#L90-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/MeanBoundsLimits.lean#L90-L94

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MiddleThirdEstimate
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeanBoundsLimits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MeanBoundsLimits
open Classical
open Formalism.FourierDecayAlt.crystallineComparison

theorem Formalism.FourierDecayAlt.P.MeanBoundsLimits.bdd_inner {f : ℕ} {Λ : AddSubgroup (V f)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (p q : V f → H) (B : ℝ) (hp : ∀ x, ‖p x‖ ≤ B) (hq : ∀ x, ‖q x‖ ≤ B)
    (σ : V f) : Bdd (fun x : Λ => inner ℂ (p x) (q ((x : V f) + σ))) := by sorry
