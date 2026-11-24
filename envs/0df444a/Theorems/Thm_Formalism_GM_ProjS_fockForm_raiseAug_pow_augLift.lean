-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_fockForm_raiseAug_pow_augLift
-- name    : Formalism.GM.ProjS.fockForm_raiseAug_pow_augLift
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:21:22.059812+00:00
-- url     : https://prove2.me/theorems/fbf55c98-e8a4-436c-b28c-df3c2924fdd4
-- title:
--   Proj S: fock Form raise Aug pow aug Lift
-- statement:
--   The Proj S construction uses the fock Form raise Aug pow aug Lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L813-L856
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L813-L856

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

theorem Formalism.GM.ProjS.fockForm_raiseAug_pow_augLift [CharZero k] (hv : M.TieVars w e zv sv) (hr : 1 ≤ r) {o n z : ℕ} {y y' : MvPolynomial σ k}
    (hy : BiHom w e o n y) (hy' : BiHom w e o n y') (hz : M.ZSFree zv sv y) (hz' : M.ZSFree zv sv y')
    (j j' : ℕ) :
    M.fockK ((((j.factorial : k))⁻¹) • ((M.tieEh w e zv sv) ^ j) (M.tieP w e zv sv o n z y))
        ((((j'.factorial : k))⁻¹) • ((M.tieEh w e zv sv) ^ j') (M.tieP w e zv sv o n z y')) =
      if j = j' then (((o + n + r + z + 1 + j - 1).choose j : ℕ) : k) * (z.factorial : k) *
        M.fockK y (tiePhi w e o n z y') else 0 := by sorry
