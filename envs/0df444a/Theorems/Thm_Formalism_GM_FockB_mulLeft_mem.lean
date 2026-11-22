-- Prove2me | Theorems.Thm_Formalism_GM_FockB_mulLeft_mem
-- name    : Formalism.GM.FockB.mulLeft_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:20:58.228331+00:00
-- url     : https://prove2.me/theorems/c1c3982c-ecc8-46e3-81e2-8ffcd61437b3
-- title:
--   Fock B: mul Left mem
-- statement:
--   The Fock B construction uses the mul Left mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L55-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FockBlocks.lean#L55-L68

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

theorem Formalism.GM.FockB.mulLeft_mem {S : Set σ} {f : MvPolynomial σ k} (hf : f ∈ Algebra.adjoin k (X '' S)) :
    LinearMap.mulLeft k f ∈ Ops S := by sorry
