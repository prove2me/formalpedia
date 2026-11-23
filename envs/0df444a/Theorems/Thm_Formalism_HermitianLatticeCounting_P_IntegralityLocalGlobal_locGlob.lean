-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_locGlob
-- name    : Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.locGlob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:54.282704+00:00
-- url     : https://prove2.me/theorems/99bcb814-3226-468c-a2c7-fed15c5e7efe
-- title:
--   Integrality Local Global: loc Glob
-- statement:
--   The Integrality Local Global construction uses the loc Glob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ComplexMultiplicationRoot.lean#L115-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ComplexMultiplicationRoot.lean#L115-L139

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
variable {E : Type} [Field E] [NumberField E]

theorem Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.locGlob (x : E) (h : ∀ P : Ideal (𝓞 E), P.IsPrime → ∃ y : 𝓞 E, y ∉ P ∧ IsInt ((y : E) * x)) :
    IsInt x := by sorry
