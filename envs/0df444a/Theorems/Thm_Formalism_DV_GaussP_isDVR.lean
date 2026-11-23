-- Prove2me | Theorems.Thm_Formalism_DV_GaussP_isDVR
-- name    : Formalism.DV.GaussP.isDVR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:53:03.397553+00:00
-- url     : https://prove2.me/theorems/0665d184-7930-4e60-8444-70880465a6ed
-- title:
--   Gauss P: is DVR
-- statement:
--   The Gauss P construction uses the is DVR property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/GaussIdealPrimality/GaussLocalizationLengthHolds.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/GaussIdealPrimality/GaussLocalizationLengthHolds.lean#L39-L53

import Definitions.Def_Formalism_GaussIdealIdentity_StatementLA
import Definitions.Def_Formalism_GaussIdealIdentity_GaussIdealPrimality_GaussLocalizationLengthHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial IsLocalRing
noncomputable section
open Formalism Formalism.DV Formalism.DV.GaussP
variable (σ O : Type) [Fintype σ] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable [(gaussIdeal σ O).IsPrime]
local notation "A" => Localization.AtPrime (gaussIdeal σ O)

theorem Formalism.DV.GaussP.isDVR : IsDiscreteValuationRing A := by sorry
