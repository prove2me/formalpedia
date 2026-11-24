-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockForm_augLift_augLift
-- name    : Formalism.GM.ProjS.fockForm_augLift_augLift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:10.011103+00:00
-- url     : https://prove2.me/theorems/ff73fa6d-9a88-47f6-b682-156fc610729f
-- title:
--   Proj S: fock Form aug Lift aug Lift
-- statement:
--   The Proj S construction uses the fock Form aug Lift aug Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L769-L796
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L769-L796

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

theorem Formalism.GM.ProjS.fockForm_augLift_augLift [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (_hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y') :
    M.fockK (M.tieP w e zv sv o n z y) (M.tieP w e zv sv o n z y') =
      (z.factorial : k) * M.fockK y (tiePhi w e o n z y') := by sorry
