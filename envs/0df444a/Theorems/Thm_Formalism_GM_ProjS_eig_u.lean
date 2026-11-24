-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eig_u
-- name    : Formalism.GM.ProjS.eig_u
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:58.819168+00:00
-- url     : https://prove2.me/theorems/882d6a06-3f25-435a-af03-f4d900502212
-- title:
--   Proj S: eig u
-- statement:
--   The Proj S construction uses the eig u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L539-L565
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L539-L565

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

theorem Formalism.GM.ProjS.eig_u (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ) (X zv ^ z * y) = ((o + z : ℕ) : k) • (X zv ^ z * y) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ) (X zv ^ z * y) = (n : k) • (X zv ^ z * y) ∧
    eulL w (X zv ^ z * y) = (o : k) • (X zv ^ z * y) := by sorry
