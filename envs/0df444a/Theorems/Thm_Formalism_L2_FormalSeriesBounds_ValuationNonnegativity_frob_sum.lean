-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_frob_sum
-- name    : Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.frob_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:19:38.851911+00:00
-- url     : https://prove2.me/theorems/7684cd19-4660-4d6d-a30e-3da9b13540c2
-- title:
--   Valuation Nonnegativity: frob sum
-- statement:
--   The Valuation Nonnegativity construction uses the frob sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L126-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/IndependenceBoundRaw.lean#L126-L138

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

theorem Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.frob_sum {ι : Type*} (s : Finset ι) (f : ι → C) (hf : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.MM ((∑ i ∈ s, f i) ^ V.l - ∑ i ∈ s, f i ^ V.l) := by sorry
