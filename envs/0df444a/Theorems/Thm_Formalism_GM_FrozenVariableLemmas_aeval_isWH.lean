-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_aeval_isWH
-- name    : Formalism.GM.FrozenVariableLemmas.aeval_isWH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:41.132909+00:00
-- url     : https://prove2.me/theorems/3a90c10c-da6f-4461-ba32-6f731dcb7157
-- title:
--   Frozen Variable Lemmas: aeval is WH
-- statement:
--   The Frozen Variable Lemmas construction uses the aeval is WH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L7-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L7-L19

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

theorem Formalism.GM.FrozenVariableLemmas.aeval_isWH {σ τ R : Type} [CommSemiring R] (w' : σ → ℕ) (w : τ → ℕ)
    (g : σ → MvPolynomial τ R) (hg : ∀ x, IsWeightedHomogeneous w (g x) (w' x))
    {f : MvPolynomial σ R} {d : ℕ} (hf : IsWeightedHomogeneous w' f d) :
    IsWeightedHomogeneous w (aeval g f) d := by sorry
