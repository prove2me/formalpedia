-- Prove2me | Theorems.Thm_Formalism_IndefR_NX_Core_thK_spec
-- name    : Formalism.IndefR.NX.Core.thK_spec
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:42:16.33437+00:00
-- url     : https://prove2.me/theorems/cc806fb7-586e-4a01-92b1-7d37b8e0feb9
-- title:
--   Core: th K spec
-- statement:
--   The Core construction uses the th K spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L208-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L208-L210

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

theorem Formalism.IndefR.NX.Core.thK_spec {Dat : Type} (j : ℕ) (σ0 : C.L0 →+* ℂ) (thC : Dat → C.W j σ0) (h : ThExists C j σ0 thC)
    (d : Dat) : IsThOf C j σ0 (thC d) (thK C j σ0 thC h d) := by sorry
