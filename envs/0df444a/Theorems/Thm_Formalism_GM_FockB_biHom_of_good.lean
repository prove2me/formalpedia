-- Prove2me | Theorems.Thm_Formalism_GM_FockB_biHom_of_good
-- name    : Formalism.GM.FockB.biHom_of_good
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:17.444049+00:00
-- url     : https://prove2.me/theorems/209580a3-2604-477b-8e95-d5b94f027ee7
-- title:
--   Fock B: bi Hom of good
-- statement:
--   The Fock B construction uses the bi Hom of good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L159-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L159-L161

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

theorem Formalism.GM.FockB.biHom_of_good [CharZero k] {o n : ℕ} {y : MvPolynomial σ k} (h : Good w e zv sv o n y) :
    BiHom w e o n y := by sorry
