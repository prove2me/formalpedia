-- Prove2me | Theorems.Thm_Formalism_GM_FockB_tieEh_eq_mulLeft
-- name    : Formalism.GM.FockB.tieEh_eq_mulLeft
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:18.598852+00:00
-- url     : https://prove2.me/theorems/1e60ee12-41b9-4cd1-8430-f8ab492d98ec
-- title:
--   Fock B: tie Eh eq mul Left
-- statement:
--   The Fock B construction uses the tie Eh eq mul Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L106-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L106-L107

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

theorem Formalism.GM.FockB.tieEh_eq_mulLeft : (M.tieEh w e zv sv : Module.End k (MvPolynomial σ k)) =
    LinearMap.mulLeft k (Ehp w e zv sv) := by sorry
