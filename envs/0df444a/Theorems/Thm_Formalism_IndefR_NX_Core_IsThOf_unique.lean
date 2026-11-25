-- Prove2me | Theorems.Thm_Formalism_IndefR_NX_Core_IsThOf_unique
-- name    : Formalism.IndefR.NX.Core.IsThOf.unique
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:41:50.456314+00:00
-- url     : https://prove2.me/theorems/e055f62e-4cc7-52c9-bb54-8d7341942a41
-- title:
--   Is Th Of: unique
-- statement:
--   The Is Th Of construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L196-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L196-L199

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

theorem Formalism.IndefR.NX.Core.IsThOf.unique {j : ℕ} {σ0 : C.L0 →+* ℂ} {thC : C.W j σ0} {x y : C.L0 ⊗[C.Ks] FmK C j}
    (hinj : Function.Injective fun z : C.L0 ⊗[C.Ks] FmK C j => (C.A j).j σ0 (inWL C j z))
    (hx : IsThOf C j σ0 thC x) (hy : IsThOf C j σ0 thC y) : x = y := by sorry
