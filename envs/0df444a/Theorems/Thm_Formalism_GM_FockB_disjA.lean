-- Prove2me | Theorems.Thm_Formalism_GM_FockB_disjA
-- name    : Formalism.GM.FockB.disjA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:43.029797+00:00
-- url     : https://prove2.me/theorems/ce5aa216-d87c-4315-8bc7-9d6220415ea6
-- title:
--   Fock B: disj A
-- statement:
--   The Fock B construction uses the disj A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L521-L556
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L521-L556

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

theorem Formalism.GM.FockB.disjA (hB : D.BlockOK) {a b : Option (Fin D.T.t)} (hab : a ≠ b) :
    Disjoint (Va (wA (r := r) D) (eA D) (zA D) (sA D) a) (Va (wA D) (eA D) (zA D) (sA D) b) := by sorry
