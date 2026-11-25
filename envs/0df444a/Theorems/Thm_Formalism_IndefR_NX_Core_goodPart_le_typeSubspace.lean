-- Prove2me | Theorems.Thm_Formalism_IndefR_NX_Core_goodPart_le_typeSubspace
-- name    : Formalism.IndefR.NX.Core.goodPart_le_typeSubspace
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:41:44.37342+00:00
-- url     : https://prove2.me/theorems/a8a0c960-c0c2-4098-b246-c2d08ad7450f
-- title:
--   Core: good Part le type Subspace
-- statement:
--   The Core construction uses the good Part le type Subspace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L160-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L160-L173

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_GramCEqTranspose
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_GoodPartLeTypeSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField TensorProduct
open Formalism Formalism.IndefR Formalism.IndefR.NX Formalism.IndefR.NX.Core
attribute [instance] RatCore.fieldBase RatCore.numberFieldBase RatCore.fKs RatCore.nfKs RatCore.algKs RatCore.crO RatCore.domO
  RatCore.grpG RatCore.finG RatCore.acgWL RatCore.modWL RatCore.modKsWL RatCore.towWL RatCore.modOLWL
  RatCore.towOLWL RatCore.modOKsWL RatCore.towOKsWL RatCore.nW RatCore.ipW
variable (C : RatCore)

theorem Formalism.IndefR.NX.Core.goodPart_le_typeSubspace (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (U : Subgroup C.G)
    (psiU : U →* (FractionRing (C.O i))ˣ) (eC : C.G → C.L0) (hcl : ∀ u g, eC (u * g * u⁻¹) = eC g) :
    V0 C i j b hst U psiU eC ≤ Fm0 C i j b hst U psiU := by sorry
