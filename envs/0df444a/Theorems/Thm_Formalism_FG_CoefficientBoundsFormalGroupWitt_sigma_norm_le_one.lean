-- Prove2me | Theorems.Thm_Formalism_FG_CoefficientBoundsFormalGroupWitt_sigma_norm_le_one
-- name    : Formalism.FG.CoefficientBoundsFormalGroupWitt.sigma_norm_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:36:50.576001+00:00
-- url     : https://prove2.me/theorems/d3ade5c7-7b1c-4c6d-a226-e544db2fdd01
-- title:
--   Coefficient Bounds Formal Group Witt: sigma norm le one
-- statement:
--   The Coefficient Bounds Formal Group Witt construction uses the sigma norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffV.lean#L13-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/CoeffV.lean#L13-L22

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CoefficientBoundsFormalGroupWitt
open Formalism.G
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem Formalism.FG.CoefficientBoundsFormalGroupWitt.sigma_norm_le_one {p q : ℕ} {σ : K →+* K} (hp : ‖(p : K)‖ ≤ 1)
    (hσ : IsFrobLift p q σ) (a : K) (ha : ‖a‖ ≤ 1) : ‖σ a‖ ≤ 1 := by sorry
