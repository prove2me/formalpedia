-- Prove2me | Theorems.Thm_Formalism_GM_ProjS_eig_P
-- name    : Formalism.GM.ProjS.eig_P
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:13.822729+00:00
-- url     : https://prove2.me/theorems/edff63ea-79b2-4ddb-b5ed-ad222ae9c75e
-- title:
--   Proj S: eig P
-- statement:
--   The Proj S construction uses the eig P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L607-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/RemoveS.lean#L607-L631

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

theorem Formalism.GM.ProjS.eig_P (hv : M.TieVars w e zv sv) (hy : BiHom w e o n y) (hz : M.ZSFree zv sv y) (c : ℕ → k) :
    eulL (Fin.cons zv w : Fin (r + 1) → σ)
      (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) =
      ((o + z : ℕ) : k) • (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) ∧
    eulL (Fin.cons sv e : Fin (r + 1) → σ)
      (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) =
      (n : k) • (∑ l ∈ range (o + 1), c l • (tieE (Fin.cons zv w : Fin (r + 1) → σ) (Fin.cons sv e) ^ l)
        ((tieF w e ^ l) (X zv ^ z * y))) := by sorry
