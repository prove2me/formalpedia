-- Prove2me | Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog
-- name    : Formalism.FG.ShiftFEAux.coeff_shiftLog
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:13:09.652675+00:00
-- url     : https://prove2.me/theorems/a737d634-3c1e-4371-9644-47bed096b8ed
-- title:
--   Shift FEAux: coeff shift Log
-- statement:
--   The Shift FEAux construction uses the coeff shift Log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/ShiftFE.lean#L20-L23

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

theorem Formalism.FG.ShiftFEAux.coeff_shiftLog (j : ZMod m) (n : ZMod m →₀ ℕ) :
    coeff n (shiftLog K l m j) = ∑ e ∈ Finset.range (n.degree + 1),
      if n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0 := by sorry
