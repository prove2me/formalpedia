-- Prove2me | Theorems.Thm_Formalism_GM_FockB_tieF_mem
-- name    : Formalism.GM.FockB.tieF_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:28.290891+00:00
-- url     : https://prove2.me/theorems/6cc79e80-3aba-46ab-9517-60d167f87c54
-- title:
--   Fock B: tie F mem
-- statement:
--   The Fock B construction uses the tie F mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L115-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L115-L119

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

theorem Formalism.GM.FockB.tieF_mem : (Formalism.GM.tieF w e : Module.End k (MvPolynomial σ k)) ∈ Ops (V w e zv sv) := by sorry
