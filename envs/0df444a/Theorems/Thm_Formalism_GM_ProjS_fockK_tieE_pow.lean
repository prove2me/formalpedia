-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_tieE_pow
-- name    : Formalism.GM.ProjS.fockK_tieE_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:43.954829+00:00
-- url     : https://prove2.me/theorems/3eaf6e5d-5321-4cc0-9df4-ba3fa518b7ac
-- title:
--   Proj S: fock K tie E pow
-- statement:
--   The Proj S construction uses the fock K tie E pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L378-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L378-L384

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

theorem Formalism.GM.ProjS.fockK_tieE_pow {r : ℕ} (w e : Fin r → σ) (l : ℕ) (g h : MvPolynomial σ k) :
    M.fockK ((tieE w e ^ l) g) h = M.fockK g ((tieF w e ^ l) h) := by sorry
