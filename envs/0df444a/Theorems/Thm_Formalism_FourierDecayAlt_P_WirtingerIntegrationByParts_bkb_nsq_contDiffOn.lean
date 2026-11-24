-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_nsq_contDiffOn
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_nsq_contDiffOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:19.600078+00:00
-- url     : https://prove2.me/theorems/f945ad95-e02b-4e2d-a3df-fd8b5fca2995
-- title:
--   Wirtinger Integration By Parts: bkb nsq cont Diff On
-- statement:
--   The Wirtinger Integration By Parts construction uses the bkb nsq cont Diff On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L562-L567
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L562-L567

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_nsq_contDiffOn {d : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (k : Fin d) (n : ℕ) :
    ContDiffOn ℝ n (fun x => Complex.normSq (fderiv ℂ g x (Pi.single k 1))) Ω := by sorry
