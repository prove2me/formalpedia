-- Prove2me | Theorems.Thm_Formalism_GM_euler_w_of_biHom
-- name    : Formalism.GM.euler_w_of_biHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:16:58.715853+00:00
-- url     : https://prove2.me/theorems/0f8720a1-1120-435a-9216-d9fd3b89f05a
-- title:
--   GM: euler w of bi Hom
-- statement:
--   The GM construction uses the euler w of bi Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L44-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L44-L54

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

theorem Formalism.GM.euler_w_of_biHom {a b : ℕ} {g : MvPolynomial σ k} (h : BiHom w e a b g) :
    (∑ c, X (w c) * pderiv (w c) g) = (a : k) • g := by sorry
