-- Prove2me | Theorems.Thm_Formalism_L2_DIV_fin_adjoin
-- name    : Formalism.L2.DIV.fin_adjoin
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:30:57.040853+00:00
-- url     : https://prove2.me/theorems/41fb5940-2540-45df-8edd-05eb205d9967
-- title:
--   DIV: fin adjoin
-- statement:
--   The DIV construction uses the fin adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Divisibility/CoeffLemmas.lean#L150-L152

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

theorem Formalism.L2.DIV.fin_adjoin {S : Set Qb} (hS : S.Finite) : FiniteDimensional ℚ (adjoin ℚ S) := by sorry
