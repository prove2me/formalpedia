-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_superset
-- name    : Formalism.GM.ProjS.fockK_superset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:27.097809+00:00
-- url     : https://prove2.me/theorems/e35d2cc4-fc9b-49b3-a9bd-0ce8d8bd53e3
-- title:
--   Proj S: fock K superset
-- statement:
--   The Proj S construction uses the fock K superset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L19-L25

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

theorem Formalism.GM.ProjS.fockK_superset (F G : MvPolynomial σ k) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    M.fockK F G = ∑ m ∈ s, F.coeff m * G.coeff m * mfac m := by sorry
