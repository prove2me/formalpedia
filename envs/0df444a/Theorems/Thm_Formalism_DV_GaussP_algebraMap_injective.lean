-- Prove2me | Theorems.Thm_Formalism_DV_GaussP_algebraMap_injective
-- name    : Formalism.DV.GaussP.algebraMap_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:51:18.96692+00:00
-- url     : https://prove2.me/theorems/669da56e-9e86-44fc-a7de-d460361bf0c0
-- title:
--   Gauss P: algebra Map injective
-- statement:
--   The Gauss P construction uses the algebra Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/GaussIdealPrimality/GaussLocalizationLengthHolds.lean#L28-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/GaussIdealPrimality/GaussLocalizationLengthHolds.lean#L28-L31

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

theorem Formalism.DV.GaussP.algebraMap_injective : Function.Injective (algebraMap O A) := by sorry
