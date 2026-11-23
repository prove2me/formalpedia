-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_main
-- name    : Formalism.FG.ShiftFEAux.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:22:17.931839+00:00
-- url     : https://prove2.me/theorems/9511c8b0-2def-477e-82a9-878062a3657d
-- title:
--   Shift FEAux: main
-- statement:
--   The Shift FEAux construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L80-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L80-L136

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.FG
open Formalism.FG.ShiftFEAux
open MvPowerSeries
variable {K : Type*} [Field K] {l m : ℕ}

theorem Formalism.FG.ShiftFEAux.main [CharZero K] (hl : l.Prime) [NeZero m] (σ : K →+* K) (j : ZMod m) :
    shiftLog K l m j - (l : K)⁻¹ • ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) = MvPowerSeries.X j := by sorry
