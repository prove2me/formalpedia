-- Prove2me | Theorems.Thm_Formalism_L2_Pj_unramBridge_holds
-- name    : Formalism.L2.Pj.unramBridge_holds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:06.127446+00:00
-- url     : https://prove2.me/theorems/ca990611-4fc3-414c-b24b-932a9824e66f
-- title:
--   Pj: unram Bridge holds
-- statement:
--   The Pj construction uses the unram Bridge holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnramBridgeHolds.lean#L9-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/UnramBridgeHolds.lean#L9-L103

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
open Formalism Formalism.L2 Formalism.L2.Pj
attribute [local instance] FractionRing.liftAlgebra

theorem Formalism.L2.Pj.unramBridge_holds : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K) := by sorry
