-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_intPol_iff
-- name    : Formalism.GM.FrozenVariableLemmas.intPol_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:16.732172+00:00
-- url     : https://prove2.me/theorems/49c844a0-5a76-41c5-9809-7a423a5857b5
-- title:
--   Frozen Variable Lemmas: int Pol iff
-- statement:
--   The Frozen Variable Lemmas construction uses the int Pol iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L204-L208
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L204-L208

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

theorem Formalism.GM.FrozenVariableLemmas.intPol_iff (F : MvPolynomial τ ℚ_[p]) :
    F ∈ M.IntPol p τ ↔ ∃ F₀ : MvPolynomial τ ℤ_[p], map (algebraMap ℤ_[p] ℚ_[p]) F₀ = F := by sorry
