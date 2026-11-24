-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_pow
-- name    : Formalism.GM.FrozenVariableLemmas.glAct_full_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:41.385875+00:00
-- url     : https://prove2.me/theorems/c4cb01f9-149d-47bc-b821-c0019effff32
-- title:
--   Frozen Variable Lemmas: gl Act full pow
-- statement:
--   The Frozen Variable Lemmas construction uses the gl Act full pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L138-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L138-L142

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableLemmas
open MvPolynomial Finset
variable (p : ℕ) [Fact p.Prime] {K r : ℕ} (L : M.Letters K) (c ρ : Fin r)

theorem Formalism.GM.FrozenVariableLemmas.glAct_full_pow (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) (hF : M.glAct p L K c ρ F = 0)
    (k : ℕ) : M.glAct p L K c ρ (F ^ k) = 0 := by sorry
