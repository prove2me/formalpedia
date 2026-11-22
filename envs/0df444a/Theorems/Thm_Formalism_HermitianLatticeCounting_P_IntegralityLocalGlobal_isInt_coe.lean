-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_coe
-- name    : Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.isInt_coe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:51.301442+00:00
-- url     : https://prove2.me/theorems/be1b394c-66a5-4ae6-a353-9a4043c5c5df
-- title:
--   Integrality Local Global: is Int coe
-- statement:
--   The Integrality Local Global construction uses the is Int coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ComplexMultiplicationRoot.lean#L103-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ComplexMultiplicationRoot.lean#L103-L107

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

theorem Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.isInt_coe (y : 𝓞 E) : IsInt (y : E) := by sorry
