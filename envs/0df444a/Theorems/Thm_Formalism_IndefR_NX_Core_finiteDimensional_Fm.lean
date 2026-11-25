-- Prove2me | Theorems.Thm_Formalism_IndefR_NX_Core_finiteDimensional_Fm
-- name    : Formalism.IndefR.NX.Core.finiteDimensional_Fm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:42:15.216954+00:00
-- url     : https://prove2.me/theorems/4d6a6a0d-dbff-4d65-8c62-a1cc6d00dec0
-- title:
--   Core: finite Dimensional Fm
-- statement:
--   The Core construction uses the finite Dimensional Fm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L81-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L81-L83

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

theorem Formalism.IndefR.NX.Core.finiteDimensional_Fm (i : C.Tw) (j : ℕ) (b : Bool) [FiniteDimensional C.Ks (FmK C j)] :
    FiniteDimensional (FractionRing (C.O i)) (Fm C i j b) := by sorry
