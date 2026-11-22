-- Prove2me | Theorems.Thm_Formalism_GM_FockB_eulL_mem
-- name    : Formalism.GM.FockB.eulL_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:20:55.943487+00:00
-- url     : https://prove2.me/theorems/7fa8b6dd-0458-4751-bb4d-0eb0c951b193
-- title:
--   Fock B: eul L mem
-- statement:
--   The Fock B construction uses the eul L mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L128-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L128-L133

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

theorem Formalism.GM.FockB.eulL_mem {s : ℕ} {S : Set σ} (t : Fin s → σ) (ht : ∀ c, t c ∈ S) :
    (ProjS.eulL t : Module.End k (MvPolynomial σ k)) ∈ Ops S := by sorry
