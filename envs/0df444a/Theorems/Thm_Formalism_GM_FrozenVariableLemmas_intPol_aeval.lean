-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_aeval
-- name    : Formalism.GM.FrozenVariableLemmas.intPol_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:51.728181+00:00
-- url     : https://prove2.me/theorems/85f1b74d-96d2-452a-95ab-fce0d7c61440
-- title:
--   Frozen Variable Lemmas: int Pol aeval
-- statement:
--   The Frozen Variable Lemmas construction uses the int Pol aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L227-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L227-L240

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
variable (p : ℕ) [Fact p.Prime] {τ : Type}

theorem Formalism.GM.FrozenVariableLemmas.intPol_aeval {υ : Type} (σ : υ → MvPolynomial τ ℚ_[p]) (hσ : ∀ x, σ x ∈ M.IntPol p τ)
    {f : MvPolynomial υ ℚ_[p]} (hf : f ∈ M.IntPol p υ) : aeval σ f ∈ M.IntPol p τ := by sorry
