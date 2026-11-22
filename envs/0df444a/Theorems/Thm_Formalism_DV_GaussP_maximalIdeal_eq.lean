-- Prove2me | Theorems.Thm_Formalism_DV_GaussP_maximalIdeal_eq
-- name    : Formalism.DV.GaussP.maximalIdeal_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T18:07:36.007962+00:00
-- url     : https://prove2.me/theorems/147b064e-c547-450e-bedc-fb293276c22a
-- title:
--   Gauss P: maximal Ideal eq
-- statement:
--   The Gauss P construction uses the maximal Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/GaussIdealPrimality/GaussLocalizationLengthHolds.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussIdealIdentity/GaussIdealPrimality/GaussLocalizationLengthHolds.lean#L22-L26

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

theorem Formalism.DV.GaussP.maximalIdeal_eq :
    IsLocalRing.maximalIdeal A = Ideal.map (algebraMap O A) (IsLocalRing.maximalIdeal O) := by sorry
