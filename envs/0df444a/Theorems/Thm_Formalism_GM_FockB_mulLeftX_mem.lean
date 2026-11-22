-- Prove2me | Theorems.Thm_Formalism_GM_FockB_mulLeftX_mem
-- name    : Formalism.GM.FockB.mulLeftX_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:23:18.409989+00:00
-- url     : https://prove2.me/theorems/c7e8c547-d753-4b37-abbe-236ef20e917b
-- title:
--   Fock B: mul Left X mem
-- statement:
--   The Fock B construction uses the mul Left X mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L48-L49

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

theorem Formalism.GM.FockB.mulLeftX_mem {S : Set σ} {u : σ} (hu : u ∈ S) : LinearMap.mulLeft k (X u : MvPolynomial σ k) ∈ Ops S := by sorry
