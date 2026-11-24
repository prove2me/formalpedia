-- Prove2me | Theorems.Thm_Formalism_GM_FockB_tieEh_mem
-- name    : Formalism.GM.FockB.tieEh_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:13:57.99981+00:00
-- url     : https://prove2.me/theorems/a9b1513b-9532-4001-9a5a-28a99fc0b8d9
-- title:
--   Fock B: tie Eh mem
-- statement:
--   The Fock B construction uses the tie Eh mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L109-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L109-L110

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

theorem Formalism.GM.FockB.tieEh_mem : (M.tieEh w e zv sv : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by sorry
