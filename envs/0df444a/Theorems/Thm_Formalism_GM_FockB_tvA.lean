-- Prove2me | Theorems.Thm_Formalism_GM_FockB_tvA
-- name    : Formalism.GM.FockB.tvA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:19.583053+00:00
-- url     : https://prove2.me/theorems/12518a7b-1f42-4947-94fc-6e552958f9aa
-- title:
--   Fock B: tv A
-- statement:
--   The Fock B construction uses the tv A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L496-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L496-L519

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} {D : BlockData N}

theorem Formalism.GM.FockB.tvA (hB : D.BlockOK) (a : Option (Fin D.T.t)) :
    M.TieVars (wA (r := r) D a) (eA D a) (zA D a) (sA D a) := by sorry
