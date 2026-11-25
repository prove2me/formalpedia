-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_even_val_add_two
-- name    : Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.even_val_add_two
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:23:29.214541+00:00
-- url     : https://prove2.me/theorems/45a9f744-ec67-4daa-a107-7cc4e68337a0
-- title:
--   Valuation Nonnegativity: even val add two
-- statement:
--   The Valuation Nonnegativity construction uses the even val add two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L212-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L212-L218

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
variable {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.even_val_add_two {d : ℕ} [NeZero d] (hd : Even d) (a : ZMod d) :
    Even (a + 2).val ↔ Even a.val := by sorry
