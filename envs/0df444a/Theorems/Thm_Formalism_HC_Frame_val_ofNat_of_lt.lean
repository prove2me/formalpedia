-- Prove2me | Theorems.Thm_Formalism_HC_Frame_val_ofNat_of_lt
-- name    : Formalism.HC.Frame.val_ofNat_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:31:52.803501+00:00
-- url     : https://prove2.me/theorems/449e465a-7074-4a9b-bfe9-25efd64048fe
-- title:
--   Frame: val of Nat of lt
-- statement:
--   The Frame construction uses the val of Nat of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L80-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L80-L81

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.Frame
variable (φ : Frame)

theorem Formalism.HC.Frame.val_ofNat_of_lt {u : ℕ} (hu : u < φ.ord) : (φ.ofNat u).val = u := by sorry
