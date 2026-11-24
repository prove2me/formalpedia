-- Prove2me | Theorems.Thm_Formalism_L2_DIV_finite_pow_eq
-- name    : Formalism.L2.DIV.finite_pow_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:31:16.72279+00:00
-- url     : https://prove2.me/theorems/5b87a76c-719f-4f7d-a148-a1b36d526af8
-- title:
--   DIV: finite pow eq
-- statement:
--   The DIV construction uses the finite pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L143-L146

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

theorem Formalism.L2.DIV.finite_pow_eq {n : ℕ} (hn : 0 < n) (a : Qb) : {z : Qb | z ^ n = a}.Finite := by sorry
