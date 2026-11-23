-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_sum
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:18.896804+00:00
-- url     : https://prove2.me/theorems/7b0aa3bd-b99b-4da1-a33f-39a636c5b775
-- title:
--   Bd: sum
-- statement:
--   The Bd construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L395-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L395-L404

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.sum {W ι : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (u : Finset ι) {f : ι → E → W} {A : ι → ℝ}
    {s : Set E} {x : E} {n : ℕ} {P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hf : ∀ i ∈ u, ContDiffOn ℝ n (f i) s) (bf : ∀ i ∈ u, Bd (f i) s x n (A i) P) :
    Bd (fun y => ∑ i ∈ u, f i y) s x n (∑ i ∈ u, A i) P := by sorry
