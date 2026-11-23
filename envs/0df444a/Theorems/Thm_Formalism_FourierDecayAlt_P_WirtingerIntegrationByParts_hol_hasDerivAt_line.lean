-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_hol_hasDerivAt_line
-- name    : Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_hasDerivAt_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:36:54.720705+00:00
-- url     : https://prove2.me/theorems/f232402b-dad1-4338-beab-43ce65158510
-- title:
--   Wirtinger Integration By Parts: hol has Deriv At line
-- statement:
--   The Wirtinger Integration By Parts construction uses the hol has Deriv At line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L46-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/WirtingerIntegrationByParts.lean#L46-L53

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
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.hol_hasDerivAt_line {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → F} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (x v : Fin d → ℂ) (ζ : ℂ) (h : x + ζ • v ∈ Ω) :
    HasDerivAt (fun ζ : ℂ => g (x + ζ • v)) (fderiv ℂ g (x + ζ • v) v) ζ := by sorry
