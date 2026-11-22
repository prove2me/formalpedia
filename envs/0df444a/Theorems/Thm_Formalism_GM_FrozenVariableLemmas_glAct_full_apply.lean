-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_apply
-- name    : Formalism.GM.FrozenVariableLemmas.glAct_full_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:21.278166+00:00
-- url     : https://prove2.me/theorems/e0ed48e6-5a02-45fa-b0c8-ff80e32b64c1
-- title:
--   Frozen Variable Lemmas: gl Act full apply
-- statement:
--   The Frozen Variable Lemmas construction uses the gl Act full apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L102-L109

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

theorem Formalism.GM.FrozenVariableLemmas.glAct_full_apply (F : MvPolynomial (Fin K × Fin r) ℚ_[p]) :
    M.glAct p L K c ρ F = ∑ i : Fin K,
      (if L.vec i then X (i, c) * pderiv (i, ρ) F else -(X (i, ρ) * pderiv (i, c) F)) := by sorry
