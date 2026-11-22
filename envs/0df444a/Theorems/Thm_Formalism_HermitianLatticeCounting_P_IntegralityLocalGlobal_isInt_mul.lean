-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_mul
-- name    : Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.isInt_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:27:35.360046+00:00
-- url     : https://prove2.me/theorems/67e99113-2e97-4dda-88c8-30418f881203
-- title:
--   Integrality Local Global: is Int mul
-- statement:
--   The Integrality Local Global construction uses the is Int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ComplexMultiplicationRoot.lean#L93-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/ComplexMultiplicationRoot.lean#L93-L97

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

theorem Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal.isInt_mul {a b : E} (ha : IsInt a) (hb : IsInt b) : IsInt (a * b) := by sorry
