-- Prove2me | Theorems.Thm_Formalism_REAL_theta_map_apply
-- name    : Formalism.REAL.theta_map_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T10:26:09.115227+00:00
-- url     : https://prove2.me/theorems/fed9b012-c76b-425d-a75b-f38e3149176e
-- title:
--   REAL: theta map apply
-- statement:
--   The REAL construction uses the theta map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L506-L510
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/RealPlaceAnalysis/RealPlaceTaylor/NoncompactGeneratorRaisesPfil.lean#L506-L510

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactGeneratorRaisesPfil
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

theorem Formalism.REAL.theta_map_apply (E : Fin n → Fin n → Module.End ℂ V) {j : ℕ} (F : Arr V n j) :
    thetaA E j F = ∑ α, u1W E α (F α) := by sorry
