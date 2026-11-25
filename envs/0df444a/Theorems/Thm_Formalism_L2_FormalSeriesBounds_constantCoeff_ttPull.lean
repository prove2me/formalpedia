-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_constantCoeff_ttPull
-- name    : Formalism.L2.FormalSeriesBounds.constantCoeff_ttPull
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:27:16.44848+00:00
-- url     : https://prove2.me/theorems/31b3036e-6029-4192-87b9-79256508cc58
-- title:
--   Formal Series Bounds: constant Coeff tt Pull
-- statement:
--   The Formal Series Bounds construction uses the constant Coeff tt Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L633-L642
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L633-L642

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

theorem Formalism.L2.FormalSeriesBounds.constantCoeff_ttPull (t : ∀ g, I g → MvPowerSeries (I g) C)
    (ht0 : ∀ g c, constantCoeff (t g c) = 0) (g : Fin 2) (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (s : I g ⊕ I (1 - g)) : constantCoeff (ttPull t g e v' s) = 0 := by sorry
