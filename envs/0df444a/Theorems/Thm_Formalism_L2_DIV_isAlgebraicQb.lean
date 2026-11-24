-- Prove2me | Theorems.Thm_Formalism_L2_DIV_isAlgebraicQb
-- name    : Formalism.L2.DIV.isAlgebraicQb
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:14.487836+00:00
-- url     : https://prove2.me/theorems/f13ce74f-e509-4f18-90d7-275a68192b8b
-- title:
--   DIV: is Algebraic Qb
-- statement:
--   The DIV construction uses the is Algebraic Qb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L49-L51

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ConjugationAtDistinguishedPlace
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_PowValCast
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoeffLemmas
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.L2.Host Formalism.DivisionValues

theorem Formalism.L2.DIV.isAlgebraicQb (LL : Fld) : Algebra.IsAlgebraic LL Qb := by sorry
