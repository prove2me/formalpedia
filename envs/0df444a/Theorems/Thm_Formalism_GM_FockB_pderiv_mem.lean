-- Prove2me | Theorems.Thm_Formalism_GM_FockB_pderiv_mem
-- name    : Formalism.GM.FockB.pderiv_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:36.890793+00:00
-- url     : https://prove2.me/theorems/5dc2d855-2239-454f-bb09-01f9e4579522
-- title:
--   Fock B: pderiv mem
-- statement:
--   The Fock B construction uses the pderiv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L51-L53

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

theorem Formalism.GM.FockB.pderiv_mem {S : Set σ} {u : σ} (hu : u ∈ S) :
    ((pderiv u : Derivation k (MvPolynomial σ k) (MvPolynomial σ k)).toLinearMap) ∈ Ops S := by sorry
