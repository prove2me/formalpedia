-- Prove2me | Theorems.Thm_Formalism_GM_FockB_tiePhi_mem
-- name    : Formalism.GM.FockB.tiePhi_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:04.60308+00:00
-- url     : https://prove2.me/theorems/02baacd5-bfa5-45c6-b933-887adcbd92a0
-- title:
--   Fock B: tie Phi mem
-- statement:
--   The Fock B construction uses the tie Phi mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L121-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L121-L126

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

theorem Formalism.GM.FockB.tiePhi_mem (o n z : ℕ) :
    (Formalism.GM.tiePhi w e o n z : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by sorry
