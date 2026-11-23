-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableLemmas_isWH_X_fst
-- name    : Formalism.GM.FrozenVariableLemmas.isWH_X_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:46.397767+00:00
-- url     : https://prove2.me/theorems/ef070ad4-f2ed-4b18-91f4-5fecccf870a8
-- title:
--   Frozen Variable Lemmas: is WH X fst
-- statement:
--   The Frozen Variable Lemmas construction uses the is WH X fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L34-L36

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

theorem Formalism.GM.FrozenVariableLemmas.isWH_X_fst {M r : ℕ} {R : Type} [CommSemiring R] (g : Fin M → ℕ) (b : Fin M) (c : Fin r) :
    IsWeightedHomogeneous (fun x : Fin M × Fin r => g x.1) (X (b, c) : MvPolynomial _ R) (g b) := by sorry
