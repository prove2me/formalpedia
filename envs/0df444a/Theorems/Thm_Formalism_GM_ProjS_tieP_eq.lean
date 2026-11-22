-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tieP_eq
-- name    : Formalism.GM.ProjS.tieP_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:31.473783+00:00
-- url     : https://prove2.me/theorems/05780338-087b-48cd-86a7-4b1b31ae454d
-- title:
--   Proj S: tie P eq
-- statement:
--   The Proj S construction uses the tie P eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L687-L692
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L687-L692

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

theorem Formalism.GM.ProjS.tieP_eq (o n z : ℕ) (y : MvPolynomial σ k) :
    M.tieP w e zv sv o n z y = ∑ l ∈ range (o + 1),
      (((-1 : k) ^ l) / (((l.factorial : k) ^ 2) * ((o + n + r + z - 1).choose l : k))) •
        (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l) ((tieF w e ^ l) (X zv ^ z * y)) := by sorry
