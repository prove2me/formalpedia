-- Prove2me | Theorems.Thm_Formalism_REAL_CasK_apply
-- name    : Formalism.REAL.CasK_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:20:43.884162+00:00
-- url     : https://prove2.me/theorems/d5fefbbc-64cf-44f5-a741-e91c82f3be41
-- title:
--   REAL: Cas K apply
-- statement:
--   The REAL construction uses the Cas K apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L332-L337
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactArrFiniteDimensional.lean#L332-L337

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

theorem Formalism.REAL.CasK_apply {j : ℕ} {ε : Fin n → Bool} (X : Fin n → Fin n → Module.End ℂ (Arr V n j))
    (G : Arr V n j) (α : Fin j → Fin n × Fin n) :
    CasK ε X G α = ∑ c, ∑ d, if ε c = ε d then X c d (X d c G) α else 0 := by sorry
