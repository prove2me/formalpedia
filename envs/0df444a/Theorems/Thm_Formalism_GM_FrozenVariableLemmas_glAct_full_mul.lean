-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_mul
-- name    : Formalism.GM.FrozenVariableLemmas.glAct_full_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:24.420209+00:00
-- url     : https://prove2.me/theorems/76cdb23b-afac-4845-aeea-3476d682c5de
-- title:
--   Frozen Variable Lemmas: gl Act full mul
-- statement:
--   The Frozen Variable Lemmas construction uses the gl Act full mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L111-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L111-L120

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

theorem Formalism.GM.FrozenVariableLemmas.glAct_full_mul (F G : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ (F * G) = F * M.glAct p L K c ρ G + G * M.glAct p L K c ρ F := by sorry
