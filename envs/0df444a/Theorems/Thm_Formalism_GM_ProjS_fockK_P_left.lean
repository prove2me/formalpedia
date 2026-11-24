-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockK_P_left
-- name    : Formalism.GM.ProjS.fockK_P_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:10.492189+00:00
-- url     : https://prove2.me/theorems/c6ed9589-afd6-4aab-9ce3-9a3766b12ba9
-- title:
--   Proj S: fock K P left
-- statement:
--   The Proj S construction uses the fock K P left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L745-L753
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L745-L753

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
variable {k σ : Type} [Field k] {r : ℕ} {w e : Fin r → σ} {zv sv : σ}

theorem Formalism.GM.ProjS.fockK_P_left (o n z : ℕ) (y Q : MvPolynomial σ k)
    (hQ : tieF (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) Q = 0) :
    M.fockK (M.tieP w e zv sv o n z y) Q = M.fockK (X zv ^ z * y) Q := by sorry
