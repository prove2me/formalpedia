-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bk_sum
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bk_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:49.605228+00:00
-- url     : https://prove2.me/theorems/f00f7c9e-9a93-405e-bf9c-2a0a38f7f765
-- title:
--   Wirtinger Integration By Parts: bk sum
-- statement:
--   The Wirtinger Integration By Parts construction uses the bk sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L532-L544
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L532-L544

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bk_sum {d : ℕ} {g : (Fin d → ℂ) → ℂ} {x : Fin d → ℂ} (hne : fderiv ℂ g x ≠ 0) :
    ∑ k, fderiv ℂ g x (Pi.single k 1) * bk g k x = 1 := by sorry
