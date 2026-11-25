-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Loc_add_natPred_succ
-- name    : Formalism.MainNotions.S.Loc.add_natPred_succ
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:51:51.487729+00:00
-- url     : https://prove2.me/theorems/b90ef290-fb29-4d2f-824a-d6f06a286a97
-- title:
--   Loc: add nat Pred succ
-- statement:
--   The Loc construction uses the add nat Pred succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/FractionFieldToGenericStalkAlgebraMapEq.lean#L267-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/FractionFieldToGenericStalkAlgebraMapEq.lean#L267-L268

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ComplexConjugate
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem Formalism.MainNotions.S.Loc.add_natPred_succ (m : ℕ) (s : ℕ+) : m + (s : ℕ) = (m + s.natPred) + 1 := by sorry
