-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_contDiff_smul_of_tsupport
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.contDiff_smul_of_tsupport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:17:53.596417+00:00
-- url     : https://prove2.me/theorems/dc3aad45-08ba-40f2-9b61-a654fd19feb3
-- title:
--   Wirtinger Integration By Parts: cont Diff smul of tsupport
-- statement:
--   The Wirtinger Integration By Parts construction uses the cont Diff smul of tsupport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L19-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L19-L32

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.contDiff_smul_of_tsupport {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℂ V] {φ : E → ℂ} {a : E → V} {Ω : Set E} {n : WithTop ℕ∞}
    (hΩ : IsOpen Ω) (hφ : ContDiffOn ℝ n φ Ω) (ha : ContDiff ℝ n a) (hsupp : tsupport a ⊆ Ω) :
    ContDiff ℝ n (fun x => φ x • a x) := by sorry
