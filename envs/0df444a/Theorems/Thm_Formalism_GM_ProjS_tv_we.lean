-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_tv_we
-- name    : Formalism.GM.ProjS.tv_we
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:46.282978+00:00
-- url     : https://prove2.me/theorems/dd56f4e2-8770-4472-9bef-c74ccb438dfe
-- title:
--   Proj S: tv we
-- statement:
--   The Proj S construction uses the tv we property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L474-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L474-L486

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

theorem Formalism.GM.ProjS.tv_we (hv : M.TieVars w e zv sv) :
    ∀ c d, (Fin.cons zv w : Fin (r + 1) → σ) c ≠ (Fin.cons sv e : Fin (r + 1) → σ) d := by sorry
