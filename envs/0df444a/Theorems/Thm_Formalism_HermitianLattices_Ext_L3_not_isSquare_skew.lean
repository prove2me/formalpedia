-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_not_isSquare_skew
-- name    : Formalism.HermitianLattices.Ext.L3.not_isSquare_skew
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:45:40.711454+00:00
-- url     : https://prove2.me/theorems/90982c8e-38d5-5014-a1a4-942da28aa643
-- title:
--   L3: not is Square skew
-- statement:
--   The L3 construction uses the not is Square skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandA.lean#L128-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MassLandA.lean#L128-L142

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandSt
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MassLandA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable (K : Type) [Field K] [NumberField K] [StarRing K]
variable {K}

theorem Formalism.HermitianLattices.Ext.L3.not_isSquare_skew (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {w : K} (hw0 : w ≠ 0) (hw : star w = -w) :
    ¬ IsSquare (⟨w * w, (mem_cmF_iff K _).2 (by rw [star_mul', hw]; ring)⟩ : cmF K) := by sorry
