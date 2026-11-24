-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_card_image
-- name    : Formalism.FrobeniusOrbits.ThickExists.card_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:16.071865+00:00
-- url     : https://prove2.me/theorems/74a11e7e-adfb-4aec-8d8c-15747480b0c8
-- title:
--   Thick Exists: card image
-- statement:
--   The Thick Exists construction uses the card image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L146-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L146-L173

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists

theorem Formalism.FrobeniusOrbits.ThickExists.card_image (L S d k : ℕ) (hL : 1 ≤ L) :
    ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))).card =
      (Behrend.sphere S d k).card := by sorry
