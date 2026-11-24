-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bkb_u_bd
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_u_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:51:55.893622+00:00
-- url     : https://prove2.me/theorems/f8d25deb-78cd-4a07-b9c4-c0f5c81be3a2
-- title:
--   Wirtinger Integration By Parts: bkb u bd
-- statement:
--   The Wirtinger Integration By Parts construction uses the bkb u bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L580-L604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L580-L604

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

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.bkb_u_bd {d q : ℕ} {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} {P : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) {x : Fin d → ℂ} (hx : x ∈ Ω)
    (hb : ∀ j : ℕ, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℂ (j + 1) g x‖ ≤ ‖fderiv ℂ g x‖ * P ^ j) (k : Fin d) :
    Bd (fun x => fderiv ℂ g x (Pi.single k 1)) Ω x q ‖fderiv ℂ g x‖ P := by sorry
