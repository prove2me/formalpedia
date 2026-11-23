-- Prove2me | Theorems.Thm_Formalism_GM_FockB_tieP_eq_Pop
-- name    : Formalism.GM.FockB.tieP_eq_Pop
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:47.230629+00:00
-- url     : https://prove2.me/theorems/87e4e2e2-4b1e-4bb6-a08f-199a68d3ff38
-- title:
--   Fock B: tie P eq Pop
-- statement:
--   The Fock B construction uses the tie P eq Pop property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L141-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L141-L143

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
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ}
variable {w e : Fin r → σ} {zv sv : σ}

theorem Formalism.GM.FockB.tieP_eq_Pop (o n z : ℕ) (y : MvPolynomial σ k) :
    M.tieP w e zv sv o n z y = Pop w e zv sv o n z y := by sorry
