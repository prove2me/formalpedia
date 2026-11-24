-- Prove2me | Theorems.Thm_Formalism_GM_FockB_pairwiseA
-- name    : Formalism.GM.FockB.pairwiseA
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:56.282316+00:00
-- url     : https://prove2.me/theorems/72168c4b-4b15-4e1e-8ce3-643737aa3faa
-- title:
--   Fock B: pairwise A
-- statement:
--   The Fock B construction uses the pairwise A property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L563-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L563-L565

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

theorem Formalism.GM.FockB.pairwiseA (hB : D.BlockOK) :
    (LA D).Pairwise fun a b => Disjoint (Va (wA (r := r) D) (eA D) (zA D) (sA D) a) (Va (wA D) (eA D) (zA D) (sA D) b) := by sorry
