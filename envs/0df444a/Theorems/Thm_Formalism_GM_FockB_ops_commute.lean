-- Prove2me | Theorems.Thm_Formalism_GM_FockB_ops_commute
-- name    : Formalism.GM.FockB.ops_commute
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:16.223624+00:00
-- url     : https://prove2.me/theorems/d7a636d1-6433-4e49-9191-fdb27def7ae1
-- title:
--   Fock B: ops commute
-- statement:
--   The Fock B construction uses the ops commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L32-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L32-L36

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
variable {k σ : Type} [Field k]

theorem Formalism.GM.FockB.ops_commute {S S' : Set σ} (hS : Disjoint S S') {T T' : Module.End k (MvPolynomial σ k)}
    (hT : T ∈ Ops S) (hT' : T' ∈ Ops S') : Commute T T' := by sorry
