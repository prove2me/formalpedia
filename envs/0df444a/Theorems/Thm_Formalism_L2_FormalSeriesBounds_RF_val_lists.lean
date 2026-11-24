-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_val_lists
-- name    : Formalism.L2.FormalSeriesBounds.RF.val_lists
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:52:27.7598+00:00
-- url     : https://prove2.me/theorems/00da8a13-b151-4207-997d-c05c6cb306f8
-- title:
--   RF: val lists
-- statement:
--   The RF construction uses the val lists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L142-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/BlockMembershipSelfConjugate.lean#L142-L161

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_MemVarsProdAll
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ContentZeroAt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

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
variable {X n}

theorem Formalism.L2.FormalSeriesBounds.RF.val_lists {FFimg : Set (∀ o, MvPolynomial (Fin n × WV (I o)) C)} {ν : ℝ} (hV : ValO X n FFimg ν) (hJ : JetProdSt)
    (F : ∀ o, Flag (X o)) (L : Orb → List (GlobalTheory d × ℝ))
    (hOK : ∀ o, ∀ q ∈ L o, q.1.AttainsOK (X o) (F o) q.2)
    (hrows : (∑ o, ((L o).map fun q => q.1.what₂ (X o).n).sum) ≤ n) (hmem : ProdMem X n F FFimg L) :
    ν ≤ ∑ o, ((L o).map Prod.snd).sum := by sorry
