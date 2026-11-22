-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eig_v
-- name    : Formalism.GM.ProjS.eig_v
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:32.168043+00:00
-- url     : https://prove2.me/theorems/849c24d6-aed3-4708-80e0-bd86084f604a
-- title:
--   Proj S: eig v
-- statement:
--   The Proj S construction uses the eig v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L591-L600
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L591-L600

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
variable {o n z : ℕ} {y : MvPolynomial σ k}

theorem Formalism.GM.ProjS.eig_v (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) (l : ℕ) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ) ((tieF w e ^ l) (X zv ^ z * y)) =
      (((o + z : ℕ) : k) - l) • (tieF w e ^ l) (X zv ^ z * y) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ) ((tieF w e ^ l) (X zv ^ z * y)) =
      ((n : k) - l) • (tieF w e ^ l) (X zv ^ z * y) ∧
    eulL w ((tieF w e ^ l) (X zv ^ z * y)) = ((o : k) - l) • (tieF w e ^ l) (X zv ^ z * y) := by sorry
