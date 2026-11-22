-- Prove2me | Theorems.Thm_Formalism_HC_Frame_mem_Psi_iff
-- name    : Formalism.HC.Frame.mem_Psi_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T17:30:49.058948+00:00
-- url     : https://prove2.me/theorems/c0aebdcb-24c7-4324-9b43-276eca94eb0f
-- title:
--   Frame: mem Psi iff
-- statement:
--   The Frame construction uses the mem Psi iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L114-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/RamificationFrobenius/TotientGaloisClasses/ZsmulGeneratorEqZeroOfProjection.lean#L114-L116

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ZsmulGeneratorEqZeroOfProjection
import Theorems.Thm_Formalism_FrobeniusOrbits_mem_Psi_iff

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

theorem Formalism.HC.Frame.mem_Psi_iff {φ : Frame} (g : φ.GG) : g ∈ φ.Psi ↔ g.1.2 = 1 := by sorry
