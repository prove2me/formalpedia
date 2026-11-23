-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_inv
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.inv
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:57.249444+00:00
-- url     : https://prove2.me/theorems/435a7368-448e-4b7e-b7ee-6e1f428803a6
-- title:
--   Bd: inv
-- statement:
--   The Bd construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L424-L477
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L424-L477

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.inv {f : E → ℝ} {s : Set E} {x : E} {n : ℕ} {κ P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hne : ∀ y ∈ s, f y ≠ 0)
    (h0 : 0 < f x) (hκ : 1 ≤ κ) (bf : Bd f s x n (κ * f x) P) :
    Bd (fun y => (f y)⁻¹) s x n ((n.factorial : ℝ) ^ 2 * κ ^ n / f x) P := by sorry
