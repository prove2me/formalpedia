-- Prove2me | Theorems.Thm_Formalism_GM_F_pow_E_pow
-- name    : Formalism.GM.F_pow_E_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T20:01:56.282814+00:00
-- url     : https://prove2.me/theorems/df7ccf79-34f5-49d5-83be-3e1d5d7a6760
-- title:
--   GM: F pow E pow
-- statement:
--   The GM construction uses the F pow E pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L220-L239
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L220-L239

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}

theorem Formalism.GM.F_pow_E_pow (hw : Function.Injective w) (he : Function.Injective e) (hwe : ∀ c d, w c ≠ e d)
    (u : MvPolynomial σ k) (a b N0 : ℕ) (hW : ∑ c, X (w c) * pderiv (w c) u = (a : k) • u)
    (hE : ∑ c, X (e c) * pderiv (e c) u = (b : k) • u) (hF : tieF w e u = 0) (hN : a + b + r = N0 + 1)
    (j l : ℕ) :
    (tieF w e ^ j) ((tieE w e ^ l) u) =
      ((l.descFactorial j * (N0 + l).descFactorial j : ℕ) : k) • (tieE w e ^ (l - j)) u := by sorry
