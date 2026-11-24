-- Prove2me | Theorems.Thm_Formalism_IndefR_NX_Core_eEnd_actG
-- name    : Formalism.IndefR.NX.Core.eEnd_actG
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:12:23.291649+00:00
-- url     : https://prove2.me/theorems/84fa19a6-46d3-4ee2-bab9-a27914b4e775
-- title:
--   Core: e End act G
-- statement:
--   The Core construction uses the e End act G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L147-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/GoodPartLeTypeSubspace.lean#L147-L158

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

theorem Formalism.IndefR.NX.Core.eEnd_actG (i : C.Tw) (j : ℕ) (b : Bool) (hst : RhoStab C j) (eC : C.G → C.L0)
    (hcl : ∀ u g, eC (u * g * u⁻¹) = eC g) (u : C.G) (x : Fm C i j b) :
    eEnd C i j b hst eC (actG C i j b hst u x) = actG C i j b hst u (eEnd C i j b hst eC x) := by sorry
