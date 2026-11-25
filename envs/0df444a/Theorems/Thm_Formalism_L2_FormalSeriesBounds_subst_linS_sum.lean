-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_subst_linS_sum
-- name    : Formalism.L2.FormalSeriesBounds.subst_linS_sum
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:52:29.124599+00:00
-- url     : https://prove2.me/theorems/3aa72a2a-a863-526f-bf21-42d5174aee51
-- title:
--   Formal Series Bounds: subst lin S sum
-- statement:
--   The Formal Series Bounds construction uses the subst lin S sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L214-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L214-L218

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
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
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type*} [Field C] {σ τ : Type*} [Fintype τ]

theorem Formalism.L2.FormalSeriesBounds.subst_linS_sum [Finite σ] (M : τ → σ → C) {ι : Type*} (s : Finset ι)
    (F : ι → MvPowerSeries σ C) :
    subst (linS M) (∑ i ∈ s, F i) = ∑ i ∈ s, subst (linS M) (F i) := by sorry
