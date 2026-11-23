-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_sum_right
-- name    : Formalism.GM.ProjS.fockK_sum_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:40.355001+00:00
-- url     : https://prove2.me/theorems/35c01e90-0df0-4581-804b-08d8449f24ce
-- title:
--   Proj S: fock K sum right
-- statement:
--   The Proj S construction uses the fock K sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L81-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L81-L84

import Definitions.Def_Formalism_MahlerMeasure_TieVars
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.ProjS
open MvPolynomial Finset
variable {k σ : Type} [Field k]

theorem Formalism.GM.ProjS.fockK_sum_right {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ k) (F : MvPolynomial σ k) :
    M.fockK F (∑ i ∈ s, f i) = ∑ i ∈ s, M.fockK F (f i) := by sorry
