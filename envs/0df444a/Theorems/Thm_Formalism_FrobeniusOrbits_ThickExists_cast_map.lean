-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_cast_map
-- name    : Formalism.FrobeniusOrbits.ThickExists.cast_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:39:35.737187+00:00
-- url     : https://prove2.me/theorems/f094ca6f-6239-4bbc-8212-18fab4ab289e
-- title:
--   Thick Exists: cast map
-- statement:
--   The Thick Exists construction uses the cast map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L74-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L74-L78

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

theorem Formalism.FrobeniusOrbits.ThickExists.cast_map (B : ℕ) {S : ℕ} (v : Fin S → ℕ) :
    ((Behrend.map B v : ℕ) : ℤ) = ∑ m, (v m : ℤ) * (B : ℤ) ^ (m : ℕ) := by sorry
