-- Prove2me | Theorems.Thm_Formalism_REAL_factorAction_apply_general
-- name    : Formalism.REAL.factorAction_apply_general
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:18.003184+00:00
-- url     : https://prove2.me/theorems/633b0181-28e2-45dc-b49f-8dccde4d753d
-- title:
--   REAL: factor Action apply general
-- statement:
--   The REAL construction uses the factor Action apply general property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L21-L25

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}

theorem Formalism.REAL.factorAction_apply_general {j : ℕ} (i : Fin j) (c d : Fin n) (F : Arr V n j) (α : Fin j → Fin n × Fin n) :
    factorAction i c d F α = (if (α i).1 = c then F (Function.update α i (d, (α i).2)) else 0) -
      (if (α i).2 = d then F (Function.update α i ((α i).1, c)) else 0) := by sorry
