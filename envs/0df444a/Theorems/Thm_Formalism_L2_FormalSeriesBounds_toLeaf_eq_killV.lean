-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_toLeaf_eq_killV
-- name    : Formalism.L2.FormalSeriesBounds.toLeaf_eq_killV
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:27:30.664631+00:00
-- url     : https://prove2.me/theorems/0d1c45c2-ba1b-4e46-95be-7962f5195324
-- title:
--   Formal Series Bounds: to Leaf eq kill V
-- statement:
--   The Formal Series Bounds construction uses the to Leaf eq kill V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L357-L366
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/LemmaMLin.lean#L357-L366

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

theorem Formalism.L2.FormalSeriesBounds.toLeaf_eq_killV {V : VF C} {d : ℕ} {J : Fin 2 → Type} (G : ∀ g, Cart V d (I g) (J g))
    (g : Fin 2) (a a' : ZMod d) (F : MvPowerSeries (WV I) C) :
    toLeaf G g a a' F = killV (OnLeafV G g a a') F := by sorry
