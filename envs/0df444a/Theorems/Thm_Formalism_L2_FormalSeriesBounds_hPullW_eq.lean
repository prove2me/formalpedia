-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_hPullW_eq
-- name    : Formalism.L2.FormalSeriesBounds.hPullW_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:52.219116+00:00
-- url     : https://prove2.me/theorems/437a0c02-306b-5b9c-b2a3-0be29b566da0
-- title:
--   Formal Series Bounds: h Pull W eq
-- statement:
--   The Formal Series Bounds construction uses the h Pull W eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L291-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L291-L299

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
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']

theorem Formalism.L2.FormalSeriesBounds.hPullW_eq (H : MvPowerSeries (WV I) C) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) :
    hPullW H (fun c => toW g (e c)) (fun b => toW (1 - g) (v' b)) = subst (linS (rowM g e v')) H := by sorry
