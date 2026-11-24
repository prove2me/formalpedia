-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_glAct_full_aeval
-- name    : Formalism.GM.FrozenVariableLemmas.glAct_full_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:52.108555+00:00
-- url     : https://prove2.me/theorems/c3af404c-f471-4904-a9c5-875f22f9a84f
-- title:
--   Frozen Variable Lemmas: gl Act full aeval
-- statement:
--   The Frozen Variable Lemmas construction uses the gl Act full aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L144-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L144-L153

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

theorem Formalism.GM.FrozenVariableLemmas.glAct_full_aeval {τ : Type} (σ : τ → MvPolynomial (Fin K × Fin r) ℚ_[p])
    (hσ : ∀ x, M.glAct p L K c ρ (σ x) = 0) (f : MvPolynomial τ ℚ_[p]) :
    M.glAct p L K c ρ (aeval σ f) = 0 := by sorry
