-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_plAt_inj
-- name    : Formalism.L2.FormalSeriesBounds.RF.plAt_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:51:17.071789+00:00
-- url     : https://prove2.me/theorems/7f0696a9-19b1-4e9b-82d3-c1e28da3994f
-- title:
--   RF: pl At inj
-- statement:
--   The RF construction uses the pl At inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L76-L81

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (n : ℕ)

theorem Formalism.L2.FormalSeriesBounds.RF.plAt_inj {K : Orb → ℕ} {what₂ : ∀ o, Fin (K o) → ℕ} {pl : (Σ o, Σ i : Fin (K o), Fin (what₂ o i)) → Fin n}
    (h : Function.Injective pl) (o : Orb) : Function.Injective (plAt n pl o) := by sorry
