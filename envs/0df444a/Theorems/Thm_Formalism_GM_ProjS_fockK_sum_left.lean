-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_sum_left
-- name    : Formalism.GM.ProjS.fockK_sum_left
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:37.33594+00:00
-- url     : https://prove2.me/theorems/8e0c91b2-432d-423d-b285-1771dc3d96c2
-- title:
--   Proj S: fock K sum left
-- statement:
--   The Proj S construction uses the fock K sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L66-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L66-L71

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

theorem Formalism.GM.ProjS.fockK_sum_left {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ k) (G : MvPolynomial σ k) :
    M.fockK (∑ i ∈ s, f i) G = ∑ i ∈ s, M.fockK (f i) G := by sorry
