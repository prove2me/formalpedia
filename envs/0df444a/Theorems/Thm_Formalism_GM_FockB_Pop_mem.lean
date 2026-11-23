-- Prove2me | Theorems.Thm_Formalism_GM_FockB_Pop_mem
-- name    : Formalism.GM.FockB.Pop_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:07.161216+00:00
-- url     : https://prove2.me/theorems/797c83b9-9764-41f9-9065-b8b331d34582
-- title:
--   Fock B: Pop mem
-- statement:
--   The Fock B construction uses the Pop mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L135-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L135-L139

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

theorem Formalism.GM.FockB.Pop_mem (o n z : ℕ) : (Pop w e zv sv o n z : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by sorry
