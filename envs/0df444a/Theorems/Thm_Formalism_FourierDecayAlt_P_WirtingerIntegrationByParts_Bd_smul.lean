-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_smul
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:39.73841+00:00
-- url     : https://prove2.me/theorems/b98dc371-2ccd-4a51-a79b-d4087b11e0b2
-- title:
--   Bd: smul
-- statement:
--   The Bd construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L360-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L360-L393

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.smul {𝕜' V : Type*} [NormedField 𝕜'] [NormedAlgebra ℝ 𝕜'] [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedSpace 𝕜' V] [IsScalarTower ℝ 𝕜' V] {f : E → 𝕜'} {h : E → V} {s : Set E} {x : E} {n : ℕ} {A B P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hh : ContDiffOn ℝ n h s)
    (bf : Bd f s x n A P) (bh : Bd h s x n B P) :
    Bd (fun y => f y • h y) s x n (2 ^ n * A * B) P := by sorry
